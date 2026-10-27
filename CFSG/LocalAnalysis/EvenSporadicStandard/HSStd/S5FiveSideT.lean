module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveSide

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

omit [Finite G] in
theorem mem_vSub_iff {w : G} (x : ↥(centralizer ({w} : Set G))) :
    x ∈ vSub w ↔ (x : G) ∈ zpowers w :=
  mem_zpowers_subtype_iff x (vElem w)

theorem outerSection_t_equiv (M : HS100Model) (h : HSOuterSetup G L t S z n v s) :
    Nonempty (OuterSection t ≃* ↥hs100R) := by
  classical
  obtain ⟨hStd, hL, hCL, hfus, -⟩ := h.setting
  have ht := h.t_mem
  have ht2 := h.t_two
  have hC : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    hStd.centralizer_le_normalizer ht ht2
  have hker : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
    hStd.centralizer_inf_centralizer_eq_zpowers hCL ht ht2
  obtain ⟨θ⟩ := M.equiv L hL
  obtain ⟨e, he⟩ := M.aut
  let D : AutModelData L ↥hs100R ↥hs100P :=
    { ι := Subgroup.inclusion hs100P_le_R
      ι_injective := Subgroup.inclusion_injective _
      θ := θ
      e := e
      he := fun w x => Subtype.ext (he w x) }
  have hsurj := rhoC_surjective D ht hC hker h.index M.card
  have hρker : (D.rhoC hC).ker = vSub t := by
    ext x
    rw [MonoidHom.mem_ker, rhoC_eq_one_iff D hC hker, mem_vSub_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hρker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (D.rhoC hC) hsurj)⟩

theorem centralizer_five_t
    (M : HS100Model)
    (h : HSOuterSetup G L t S z n v s) {r u₁ u₂ : G} (tr : FiveTriple L v r u₁ u₂) :
    Nonempty (↥(centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G)) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htt : t * t = 1 := h.t_sq
  have hto : orderOf t = 2 := orderOf_eq_two_of_sq htt h.t_ne_one
  have htcomm : ∀ x ∈ L, x * t = t * x := fun x hx => mem_centralizer_iff.1 h.t_mem x hx
  have htL : t ∉ L := by
    intro htl
    have hZ : center L = ⊥ := M.center_eq_bot L h.setting.2.1
    have h1 : (⟨t, htl⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (htcomm g g.2)
    rw [hZ, mem_bot] at h1
    exact h.t_ne_one (congrArg Subtype.val h1)
  obtain ⟨θt⟩ := outerSection_t_equiv M h
  have hzr : r ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 (htcomm r tr.r_mem)
  have hwc : u₁ * u₂ ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 := htcomm u₁ tr.u₁_mem
    have h2 := htcomm u₂ tr.u₂_mem
    calc u₁ * u₂ * t = u₁ * (u₂ * t) := by rw [mul_assoc]
      _ = u₁ * (t * u₂) := by rw [h2]
      _ = (u₁ * t) * u₂ := by rw [mul_assoc]
      _ = (t * u₁) * u₂ := by rw [h1]
      _ = t * (u₁ * u₂) := by rw [mul_assoc]
  have hword : orderOf (u₁ * u₂) = 3 := orderOf_eq_prime tr.u_cube tr.u_ne
  have hrbar : orderOf (rBar hzr) = 5 := orderOf_sectionMk htt (by norm_num) hzr tr.r_ord
  have hwbar := orderOf_sectionMk htt (p := 3) (by norm_num) hwc hword
  have hwr : (QuotientGroup.mk (⟨u₁ * u₂, hwc⟩ : ↥(centralizer ({t} : Set G))) :
      OuterSection t) ∈ centralizer ({rBar hzr} : Set (OuterSection t)) := by
    rw [mem_centralizer_singleton_iff]
    change (QuotientGroup.mk _ : OuterSection t) * QuotientGroup.mk (rElem hzr) =
      QuotientGroup.mk (rElem hzr) * QuotientGroup.mk _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    show u₁ * u₂ * r = r * (u₁ * u₂)
    rw [mul_assoc, tr.u₂_r, ← mul_assoc, tr.u₁_r, mul_assoc]
  have h3 : 3 ∣ Nat.card ↥(centralizer ({rBar hzr} : Set (OuterSection t))) := by
    have := orderOf_dvd_natCard (⟨_, hwr⟩ : ↥(centralizer ({rBar hzr} : Set (OuterSection t))))
    rwa [Subgroup.orderOf_mk, hwbar] at this
  obtain ⟨e⟩ := five_centralizer_of_equiv_R θt hrbar h3
  obtain ⟨ψ, hψs, hψk⟩ := exists_psi_of_section htt h.t_ne_one hzr tr.r_ord e
  have hQmem : ∀ g : G, g * t = t * g → g * r = r * g →
      g ∈ centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G) := fun g h1 h2 =>
    mem_inf.2 ⟨mem_centralizer_singleton_iff.2 h1, mem_centralizer_singleton_iff.2 h2⟩
  have htQ := hQmem t rfl (htcomm r tr.r_mem).symm
  have hrQ := hQmem r (htcomm r tr.r_mem) rfl
  have hvQ := hQmem v h.t_comm_v.symm tr.r_comm.symm
  have hu₁Q := hQmem u₁ (htcomm u₁ tr.u₁_mem) tr.u₁_r
  have hu₂Q := hQmem u₂ (htcomm u₂ tr.u₂_mem) tr.u₂_r
  refine exists_mulEquiv_of_central_five (z := ⟨t, htQ⟩) (r := ⟨r, hrQ⟩) ?_ ?_ ?_ ?_ ψ hψs
    (fun q => (hψk q).trans (mem_zpowers_subtype_iff q ⟨t, htQ⟩).symm)
    (x := ⟨v, hvQ⟩) (y₁ := ⟨u₁, hu₁Q⟩) (y₂ := ⟨u₂, hu₂Q⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 g.2).1)
  · exact (Subgroup.orderOf_mk t htQ).trans hto
  · rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 g.2).2)
  · exact (Subgroup.orderOf_mk r hrQ).trans tr.r_ord
  · exact Subtype.ext h.ctx.v_sq
  · rw [mem_zpowers_subtype_iff]
    exact not_mem_zpowers_of_sq htt h.v_ne_one h.t_ne_v.symm
  · exact Subtype.ext tr.u₁_sq
  · exact Subtype.ext tr.u₂_sq
  · exact Subtype.ext (by simpa using tr.u_cube)
  · rw [mem_zpowers_subtype_iff]
    refine not_mem_zpowers_of_sq htt tr.u_ne ?_
    intro hh
    have hh' : u₁ * u₂ = t := hh
    exact htL (hh' ▸ L.mul_mem tr.u₁_mem tr.u₂_mem)
  · exact Subtype.ext tr.u₁_comm.symm
  · exact Subtype.ext tr.u₂_comm.symm

end CFSG.EvenSporadicStandard.HSStd
