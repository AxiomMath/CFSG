module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Core

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {W : Type*} [AddCommGroup W] {m n : ℕ}

theorem fixA_le_comp {G G' : Type*} [Group G] [Group G'] (r : G →* AddMonoid.End W)
    (f : G' →* G) : fixA r ≤ fixA (r.comp f) := fun _ hw g => hw (f g)

theorem commA_comp_le {G G' : Type*} [Group G] [Group G'] (r : G →* AddMonoid.End W)
    (f : G' →* G) : commA (r.comp f) ≤ commA r :=
  commA_le fun g v => sub_mem_commA r (f g) v

section Section

variable {G : Type*} [Group G]

theorem commA_invariant (r : G →* AddMonoid.End W) : ∀ g, ∀ u ∈ commA r, r g u ∈ commA r :=
  fun g _ hu => apply_mem_commA r g hu

@[expose] def secKer (r : G →* AddMonoid.End W) : AddSubgroup ↥(commA r) :=
  ((commA r) ⊓ fixA r).addSubgroupOf (commA r)

theorem mem_secKer {r : G →* AddMonoid.End W} {u : ↥(commA r)} :
    u ∈ secKer r ↔ (u : W) ∈ fixA r :=
  ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩

theorem secKer_invariant (r : G →* AddMonoid.End W) :
    ∀ g, ∀ c ∈ secKer r, restrictEnd r (commA r) (commA_invariant r) g c ∈ secKer r := by
  intro g c hc
  rw [mem_secKer] at hc ⊢
  change r g (c : W) ∈ fixA r
  rw [hc g]
  exact hc

abbrev Sect (r : G →* AddMonoid.End W) : Type _ := ↥(commA r) ⧸ secKer r

@[expose] def sectEnd (r : G →* AddMonoid.End W) : G →* AddMonoid.End (Sect r) :=
  quotEnd (restrictEnd r (commA r) (commA_invariant r)) (secKer r) (secKer_invariant r)

theorem sectEnd_mk (r : G →* AddMonoid.End W) (g : G) (u : ↥(commA r)) :
    sectEnd r g (u : Sect r) =
      ((⟨r g u, apply_mem_commA r g u.2⟩ : ↥(commA r)) : Sect r) :=
  rfl

end Section

theorem natShapeA_section (ι : Fin m ↪ Fin n) (hm : 4 ≤ m)
    (r : alternatingGroup (Fin n) →* AddMonoid.End W)
    (h : NatShapeA (r.comp (altLift ι)) (alternatingGroup (Fin m)).subtype) :
    NatShapeA ((sectEnd r).comp (altLift ι)) (alternatingGroup (Fin m)).subtype := by
  set U := commA r with hU
  set rK := r.comp (altLift ι) with hrK
  obtain ⟨πK, hπK, hkerK, heqK⟩ := h.canonical hm fun σ hσ => ⟨⟨σ, hσ⟩, rfl⟩
  have hPU : commA rK ≤ U := commA_comp_le r (altLift ι)
  let j : ↥(commA rK) →+ Sect r := (QuotientAddGroup.mk' (secKer r)).comp (AddSubgroup.inclusion hPU)
  have hj : ∀ p, j p = ((AddSubgroup.inclusion hPU p : ↥U) : Sect r) := fun p => rfl
  have hkerle : j.ker ≤ πK.ker := by
    intro p hp
    rw [AddMonoidHom.mem_ker, hj, QuotientAddGroup.eq_zero_iff, mem_secKer] at hp
    rw [AddMonoidHom.mem_ker, hkerK]
    exact fixA_le_comp r (altLift ι) hp
  let πX : ↥j.range →+ altHeart m :=
    (QuotientAddGroup.lift j.ker πK hkerle).comp
      (QuotientAddGroup.quotientKerEquivRange j).symm.toAddMonoidHom
  have hπX : ∀ p, πX ⟨j p, p, rfl⟩ = πK p := by
    intro p
    have : (QuotientAddGroup.quotientKerEquivRange j).symm ⟨j p, p, rfl⟩ =
        ((p : ↥(commA rK)) : ↥(commA rK) ⧸ j.ker) := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    change QuotientAddGroup.lift j.ker πK hkerle
      ((QuotientAddGroup.quotientKerEquivRange j).symm ⟨j p, p, rfl⟩) = πK p
    rw [this]
    rfl
  have hjact : ∀ (σ : alternatingGroup (Fin m)) (p : ↥(commA rK)),
      sectEnd r (altLift ι σ) (j p) = j ⟨rK σ p, apply_mem_commA rK σ p.2⟩ := fun σ p => rfl
  refine ⟨πX.ker.map j.range.subtype, j.range, AddSubgroup.map_subtype_le _, ?_, ?_, πX, ?_, ?_,
    ?_⟩
  · rintro σ _ ⟨⟨_, p, rfl⟩, hy, rfl⟩
    have hy' : πX ⟨j p, p, rfl⟩ = 0 := hy
    rw [hπX, hkerK] at hy'
    change sectEnd r (altLift ι σ) (j p) = j p
    rw [hjact]
    congr 1
    exact Subtype.ext (hy' σ)
  · intro σ x
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
    exact ⟨⟨rK σ u - u, sub_mem_commA rK σ u⟩, rfl⟩
  · intro z
    obtain ⟨p, rfl⟩ := hπK z
    exact ⟨⟨j p, p, rfl⟩, hπX p⟩
  · ext x
    rw [AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rw [← Subtype.ext hyx]
      exact hy
  · rintro σ ⟨_, p, rfl⟩ ⟨y, hy⟩ hxy
    obtain ⟨p', rfl⟩ := hy
    have hp' : p' - ⟨rK σ p, apply_mem_commA rK σ p.2⟩ ∈ j.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero]
      exact hxy
    have h1 := hkerle hp'
    rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero] at h1
    change πX ⟨j p', p', rfl⟩ = _
    rw [hπX, hπX, h1]
    exact heqK σ p _ rfl

theorem natShapeA_of_stab (hW : ∀ w : W, w + w = 0) (hn : 7 ≤ n) (ι : Fin m ↪ Fin n)
    (hmn : m + 1 = n) (r : alternatingGroup (Fin n) →* AddMonoid.End W)
    (h : NatShapeA (r.comp (altLift ι)) (alternatingGroup (Fin m)).subtype) :
    NatShapeA r (alternatingGroup (Fin n)).subtype := by
  classical
  have hperf : commutator (alternatingGroup (Fin n)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  let _ : Module (ZMod 2) (Sect r) := AddCommGroup.zmodModule (n := 2) fun x => by
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [two_nsmul, ← QuotientAddGroup.mk_add]
    have : u + u = 0 := Subtype.ext (hW u)
    rw [this, QuotientAddGroup.mk_zero]
  have hirr : ∀ Y : AddSubgroup (Sect r), (∀ g, ∀ y ∈ Y, sectEnd r g y ∈ Y) →
      Y = ⊥ ∨ Y = ⊤ := by
    intro Y hY
    let Ŷ : AddSubgroup W := (Y.comap (QuotientAddGroup.mk' (secKer r))).map (commA r).subtype
    have hŶ : ∀ g, ∀ y ∈ Ŷ, r g y ∈ Ŷ := by
      rintro g _ ⟨u, hu, rfl⟩
      exact ⟨⟨r g u, apply_mem_commA r g u.2⟩, hY g _ hu, rfl⟩
    rcases alt_dichotomy (by omega) ι hmn h Ŷ hŶ with htriv | hco
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
      rw [AddSubgroup.mem_bot, QuotientAddGroup.eq_zero_iff, mem_secKer]
      exact fun g => htriv g u ⟨u, hx, rfl⟩
    · right
      rw [eq_top_iff]
      intro x _
      obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨u', hu', hu'u⟩ := commA_le hco u.2
      rw [← Subtype.ext hu'u]
      exact hu'
  have hfix : ∀ x : Sect r, (∀ g, sectEnd r g x = x) → x = 0 := by
    intro x hx
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hsub : ∀ g, r g u - u ∈ fixA r := fun g => by
      have h1 := hx g
      rw [sectEnd_mk, QuotientAddGroup.eq, mem_secKer] at h1
      have h3 : (r g u - u : W) =
          -(((-(⟨r g u, apply_mem_commA r g u.2⟩ : ↥(commA r)) + u : ↥(commA r)) : W)) := by
        simp only [AddSubgroup.coe_neg, AddSubgroup.coe_add]
        abel
      rw [h3]
      exact (fixA r).neg_mem h1
    have hu := apply_eq_of_perfect hperf r {(u : W)} (fun g w hw g' => by
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hsub g g')
    rw [QuotientAddGroup.eq_zero_iff, mem_secKer]
    exact fun g => hu g u rfl
  obtain ⟨Θ, hΘ⟩ := exists_heartEquiv_of_shape hn ι hmn (sectEnd r) hirr hfix
    (natShapeA_section ι (by omega) r h)
  refine ⟨(commA r) ⊓ fixA r, commA r, inf_le_left, fun g w hw => hw.2 g,
    fun g w => sub_mem_commA r g w,
    Θ.symm.toAddMonoidHom.comp (QuotientAddGroup.mk' (secKer r)), ?_, ?_, ?_⟩
  · intro z
    obtain ⟨u, hu⟩ := QuotientAddGroup.mk_surjective (Θ z)
    refine ⟨u, ?_⟩
    change Θ.symm (u : Sect r) = z
    rw [hu, AddEquiv.symm_apply_apply]
  · ext u
    rw [AddMonoidHom.mem_ker]
    change Θ.symm (u : Sect r) = 0 ↔ u ∈ secKer r
    rw [← QuotientAddGroup.eq_zero_iff]
    constructor
    · intro hu
      have := congrArg Θ hu
      rwa [AddEquiv.apply_symm_apply, map_zero] at this
    · intro hu
      rw [hu, map_zero]
  · intro g u v huv
    have hv : v = ⟨r g u, apply_mem_commA r g u.2⟩ := Subtype.ext huv
    change Θ.symm (v : Sect r) = altAct _ (Θ.symm (u : Sect r))
    rw [hv, ← sectEnd_mk]
    apply Θ.injective
    rw [AddEquiv.apply_symm_apply]
    change _ = Θ (altAct (g : Perm (Fin n)) (Θ.symm (u : Sect r)))
    rw [hΘ, AddEquiv.apply_symm_apply]

theorem natShape_of_stab {V : Type*} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (hn : 7 ≤ n)
    (ι : Fin m ↪ Fin n) (hmn : m + 1 = n) (ρ : alternatingGroup (Fin n) →* MulAut V)
    (h : NatShape (ρ.comp (altLift ι)) (alternatingGroup (Fin m)).subtype) :
    NatShape ρ (alternatingGroup (Fin n)).subtype := by
  rw [natShape_iff_natShapeA] at h ⊢
  rw [← MonoidHom.comp_assoc] at h
  refine natShapeA_of_stab (fun w => ?_) hn ι hmn (autToEnd.comp ρ) h
  change Additive.ofMul (Additive.toMul w * Additive.toMul w) = Additive.ofMul 1
  rw [← pow_two, hV]

theorem exists_embedding_factor {k l : ℕ} (ι : Fin k ↪ Fin n) (ι₂ : Fin l ↪ Fin n)
    (h : ∀ i, ι i ∈ Set.range ι₂) : ∃ ι₁ : Fin k ↪ Fin l, ι₁.trans ι₂ = ι := by
  choose f hf using h
  refine ⟨⟨f, fun i j hij => ι.injective (by rw [← hf i, ← hf j, hij])⟩, ?_⟩
  ext i
  exact congrArg Fin.val (hf i)

theorem natShape_of_stab₂ {V : Type*} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) {k : ℕ}
    (hn : 8 ≤ n) (ι : Fin k ↪ Fin n) (hkn : k + 2 = n) (ρ : alternatingGroup (Fin n) →* MulAut V)
    (h : NatShape (ρ.comp (altLift ι)) (alternatingGroup (Fin k)).subtype) :
    NatShape ρ (alternatingGroup (Fin n)).subtype := by
  obtain rfl : n = k + 1 + 1 := by omega
  obtain ⟨a, ha⟩ := exists_notMem_of_card_lt (Finset.univ.map ι) (by simp)
  let ι₂ : Fin (k + 1) ↪ Fin (k + 1 + 1) := Fin.succAboveEmb a
  obtain ⟨ι₁, hι₁⟩ := exists_embedding_factor ι ι₂ fun i => by
    change ι i ∈ Set.range a.succAbove
    rw [Fin.range_succAbove]
    intro h
    exact ha ((Set.mem_singleton_iff.1 h) ▸ Finset.mem_map_of_mem ι (Finset.mem_univ i))
  refine natShape_of_stab hV (by omega) ι₂ rfl ρ
    (natShape_of_stab hV (by omega) ι₁ rfl (ρ.comp (altLift ι₂)) ?_)
  rw [MonoidHom.comp_assoc, ← altLift_trans, hι₁]
  exact h

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
