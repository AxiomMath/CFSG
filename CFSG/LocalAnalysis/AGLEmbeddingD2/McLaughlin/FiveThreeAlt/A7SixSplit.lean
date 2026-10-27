module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.AltCocycle
public import CFSG.RankThree.PartTwo.Sec19.Item194Proof

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.HardMathSupport.Cooperstein.Coordinator

@[expose] def wEven (k : Fin 7) : evenWeight 7 :=
  ⟨fun i => 1 + (if i = k then 1 else 0), by
    rw [evenWeight, AddMonoidHom.mem_ker]
    simp only [AddMonoidHom.mk'_apply, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    decide⟩

theorem wEven_apply (k i : Fin 7) :
    ((wEven k : evenWeight 7) : Fin 7 → ZMod 2) i = 1 + (if i = k then 1 else 0) := rfl

theorem evenWeightPerm_wEven (σ : Perm (Fin 7)) (k : Fin 7) :
    evenWeightPerm σ (wEven k) = wEven (σ k) := by
  refine Subtype.ext (funext fun i => ?_)
  rw [evenWeightPerm_apply, wEven_apply, wEven_apply]
  have : (σ⁻¹ i = k) ↔ (i = σ k) := by
    constructor
    · rintro h; rw [← h]; simp
    · rintro h; rw [h]; simp
  simp only [this]

@[expose] noncomputable def wHeart (k : Fin 7) : altHeart 7 := QuotientAddGroup.mk (wEven k)

theorem altAct_wHeart (σ : Perm (Fin 7)) (k : Fin 7) : altAct σ (wHeart k) = wHeart (σ k) := by
  unfold wHeart
  rw [altAct_mk, evenWeightPerm_wEven]

theorem nsmul_mod_two {M : Type} [AddCommGroup M] (h2 : ∀ x : M, x + x = 0) (m : ℕ) (x : M) :
    (m % 2) • x = m • x := by
  conv_rhs => rw [← Nat.mod_add_div m 2, add_smul, mul_comm, mul_smul, two_nsmul, h2, nsmul_zero,
    add_zero]

section Split

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

theorem stab_fixes_lift (ρ : alternatingGroup (Fin 7) →* Module.End (ZMod 2) M) (N : AddSubgroup M)
    (hN : ∀ a : alternatingGroup (Fin 7), ∀ x ∈ N, ρ a x ∈ N)
    (π : ↥N →+ altHeart 7)
    (hπe : ∀ (a : alternatingGroup (Fin 7)) (x : ↥N),
      π ⟨ρ a x, hN a x x.2⟩ = altAct (a : Perm (Fin 7)) (π x))
    (hπk : ∀ x : ↥N, π x = 0 → ∀ a, ρ a x = x)
    {n0 : M} (hn0N : n0 ∈ N) (hn0 : π ⟨n0, hn0N⟩ = wHeart 0)
    (a : alternatingGroup (Fin 7)) (ha : (a : Perm (Fin 7)) 0 = 0) : ρ a n0 = n0 := by
  have hψk : ∀ a : alternatingGroup (Fin 7), (a : Perm (Fin 7)) 0 = 0 →
      ∀ b, ρ b (ρ a n0 - n0) = ρ a n0 - n0 := by
    intro a ha b
    have hmem : ρ a n0 - n0 ∈ N := N.sub_mem (hN a n0 hn0N) hn0N
    have e1 : (⟨ρ a n0 - n0, hmem⟩ : ↥N) = ⟨ρ a n0, hN a n0 hn0N⟩ - ⟨n0, hn0N⟩ := rfl
    have h0 : π ⟨ρ a n0 - n0, hmem⟩ = 0 := by
      rw [e1, map_sub, hπe a ⟨n0, hn0N⟩, hn0, altAct_wHeart, ha, sub_self]
    exact hπk ⟨ρ a n0 - n0, hmem⟩ h0 b
  have hψmul : ∀ a b : alternatingGroup (Fin 7), (a : Perm (Fin 7)) 0 = 0 →
      (b : Perm (Fin 7)) 0 = 0 →
      ρ (a * b) n0 - n0 = (ρ a n0 - n0) + (ρ b n0 - n0) := by
    intro a b ha hb
    have h2 : ρ (a * b) n0 = ρ a (ρ b n0) := by rw [map_mul]; rfl
    have h3 : ρ b n0 = (ρ b n0 - n0) + n0 := by abel
    have h4 := hψk b hb a
    rw [h2]
    conv_lhs => rw [h3]
    rw [map_add, h4]
    abel
  set s : Finset (Fin 7) := ({0} : Finset (Fin 7))ᶜ with hs
  have hcard : 5 ≤ Nat.card s := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hs, Finset.card_compl, Fintype.card_fin]
    simp
  have h0s : (0 : Fin 7) ∉ s := by simp [hs]
  have hfix : ∀ g : alternatingGroup s,
      (alternatingGroup.ofSubtype s g : Perm (Fin 7)) 0 = 0 := fun g => by
    rw [alternatingGroup.coe_ofSubtype]
    exact Perm.ofSubtype_apply_of_not_mem _ h0s
  let ψ' : alternatingGroup s →* Multiplicative M :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd
      (ρ (alternatingGroup.ofSubtype s g) n0 - n0)) fun g g' => by
      rw [map_mul (alternatingGroup.ofSubtype s) g g', hψmul _ _ (hfix g) (hfix g')]
      rfl
  have hsupp : (a : Perm (Fin 7)).support ⊆ s := by
    intro i hi
    rw [Perm.mem_support] at hi
    simp only [hs, Finset.mem_compl, Finset.mem_singleton]
    exact fun h => hi (by rw [h]; exact ha)
  obtain ⟨g, hg⟩ := (alternatingGroup.mem_range_ofSubtype_iff s a).2 hsupp
  have hψg : ψ' g = 1 := MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker ψ'
    (by rw [commutator_alternatingGroup_eq_top hcard]; exact Subgroup.mem_top g))
  have h3 : ρ a n0 - n0 = 0 := by
    change Multiplicative.ofAdd (ρ (alternatingGroup.ofSubtype s g) n0 - n0) = 1 at hψg
    rw [hg, ofAdd_eq_one] at hψg
    exact hψg
  exact sub_eq_zero.1 h3

theorem exists_alt_apply_zero (k : Fin 7) :
    ∃ a : alternatingGroup (Fin 7), (a : Perm (Fin 7)) 0 = k := by
  by_cases hk : k = 0
  · exact ⟨1, by simp [hk]⟩
  · obtain ⟨p, hp0, hpk, -, -⟩ := exists_ne_four (by norm_num : 5 ≤ 7) 0 k 0 0
    obtain ⟨g, hg, -, hg0⟩ := exists_alt_fix_apply_eq (by norm_num : 5 ≤ 7) (k := p) (j := 0)
      (i := k) (Ne.symm hp0) (Ne.symm hpk)
    exact ⟨⟨g, hg⟩, hg0⟩

theorem mem_evenWeight_iff (e : Fin 7 → ZMod 2) : e ∈ evenWeight 7 ↔ ∑ k, e k = 0 := by
  rw [evenWeight, AddMonoidHom.mem_ker]
  rfl

theorem injective_of_natural_section
    (ρ : alternatingGroup (Fin 7) →* Module.End (ZMod 2) M) (N : AddSubgroup M)
    (hN : ∀ a : alternatingGroup (Fin 7), ∀ x ∈ N, ρ a x ∈ N)
    (π : ↥N →+ altHeart 7) (hπs : Function.Surjective π)
    (hπe : ∀ (a : alternatingGroup (Fin 7)) (x : ↥N),
      π ⟨ρ a x, hN a x x.2⟩ = altAct (a : Perm (Fin 7)) (π x))
    (hπk : ∀ x : ↥N, π x = 0 → ∀ a, ρ a x = x)
    (hperf : N ≤ AddSubgroup.closure {y | ∃ a, ∃ z ∈ N, y = ρ a z - z}) :
    Function.Injective π := by
  classical
  have h2 : ∀ x : M, x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  obtain ⟨n0', hn0'⟩ := hπs (wHeart 0)
  have hn0N : (n0' : M) ∈ N := n0'.2
  have hn0 : π ⟨n0', hn0N⟩ = wHeart 0 := hn0'
  have hfix0 := stab_fixes_lift ρ N hN π hπe hπk hn0N hn0
  choose a ha using exists_alt_apply_zero
  let nk : Fin 7 → M := fun k => ρ (a k) n0'
  have hnkN : ∀ k, nk k ∈ N := fun k => hN _ _ hn0N
  have hρn : ∀ (b : alternatingGroup (Fin 7)) (k : Fin 7), ρ b (nk k) = nk ((b : Perm (Fin 7)) k) := by
    intro b k
    have hc : (((a ((b : Perm (Fin 7)) k))⁻¹ * (b * a k) : alternatingGroup (Fin 7)) :
        Perm (Fin 7)) 0 = 0 := by
      have h1 : ((a ((b : Perm (Fin 7)) k) : Perm (Fin 7)))⁻¹ ((b : Perm (Fin 7)) k) = 0 := by
        rw [Perm.inv_eq_iff_eq, ha]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
      rw [ha k, h1]
    have h3 := hfix0 _ hc
    show ρ b (ρ (a k) n0') = ρ (a ((b : Perm (Fin 7)) k)) n0'
    calc ρ b (ρ (a k) n0') = ρ (b * a k) n0' := by rw [map_mul]; rfl
      _ = ρ (a ((b : Perm (Fin 7)) k) * ((a ((b : Perm (Fin 7)) k))⁻¹ * (b * a k))) n0' := by
          congr 2; group
      _ = ρ (a ((b : Perm (Fin 7)) k)) (ρ ((a ((b : Perm (Fin 7)) k))⁻¹ * (b * a k)) n0') := by
          rw [map_mul]; rfl
      _ = ρ (a ((b : Perm (Fin 7)) k)) n0' := by rw [h3]
  have hπn : ∀ k, π ⟨nk k, hnkN k⟩ = wHeart k := by
    intro k
    have := hπe (a k) ⟨n0', hn0N⟩
    rw [hn0, altAct_wHeart, ha k] at this
    exact this
  let F : (Fin 7 → ZMod 2) →+ M :=
    { toFun := fun e => ∑ k, (e k).val • nk k
      map_zero' := by simp
      map_add' := fun e e' => by
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ZMod.val_add, nsmul_mod_two h2 ((e k).val + (e' k).val) (nk k), add_nsmul] }
  have hFapp : ∀ e, F e = ∑ k, (e k).val • nk k := fun e => rfl
  have hFN : ∀ e, F e ∈ N := fun e => by
    rw [hFapp]
    exact N.sum_mem fun k _ => N.nsmul_mem (hnkN k) _
  have hFρ : ∀ (b : alternatingGroup (Fin 7)) (e : Fin 7 → ZMod 2),
      ρ b (F e) = F (fun k => e ((b : Perm (Fin 7))⁻¹ k)) := by
    intro b e
    rw [hFapp, hFapp, map_sum]
    simp only [map_nsmul, hρn]
    exact (Finset.sum_congr rfl fun x _ => by simp).trans
      (Equiv.sum_comp (b : Perm (Fin 7)) (fun j => (e ((b : Perm (Fin 7))⁻¹ j)).val • nk j))
  let _ : AddCommGroup (altHeart 7) :=
    { (inferInstance : AddGroup (altHeart 7)) with
      add_comm := fun a b => by
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
        obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective b
        rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add]
        exact congrArg _ (Subtype.ext (add_comm (x : Fin 7 → ZMod 2) y)) }
  have hπF : ∀ δ : evenWeight 7,
      π ⟨F (δ : Fin 7 → ZMod 2), hFN _⟩ = (QuotientAddGroup.mk δ : altHeart 7) := by
    intro δ
    have e1 : (⟨F (δ : Fin 7 → ZMod 2), hFN _⟩ : ↥N) =
        ∑ k, ((δ : Fin 7 → ZMod 2) k).val • (⟨nk k, hnkN k⟩ : ↥N) := by
      apply Subtype.ext
      show F (δ : Fin 7 → ZMod 2) = ((∑ k, ((δ : Fin 7 → ZMod 2) k).val •
        (⟨nk k, hnkN k⟩ : ↥N) : ↥N) : M)
      rw [AddSubmonoidClass.coe_finsetSum, hFapp]
      simp
    rw [e1, map_sum]
    simp only [map_nsmul, hπn]
    have e3 : (∑ k, ((δ : Fin 7 → ZMod 2) k).val • wEven k : evenWeight 7) = δ := by
      apply Subtype.ext
      funext i
      have hs : ∑ k, (δ : Fin 7 → ZMod 2) k = 0 := (mem_evenWeight_iff _).1 δ.2
      rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
      simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, wEven_apply, nsmul_eq_mul,
        ZMod.natCast_zmod_val, mul_add, mul_one, Finset.sum_add_distrib, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, hs, zero_add]
    have e2 : ∑ k, ((δ : Fin 7 → ZMod 2) k).val • wHeart k =
        QuotientAddGroup.mk' (evenWeightOnes 7) (∑ k, ((δ : Fin 7 → ZMod 2) k).val • wEven k) := by
      rw [map_sum]
      simp only [map_nsmul]
      rfl
    rw [e2, e3]
    rfl
  let S : AddSubgroup M := (evenWeight 7).map F
  have hNS : N ≤ S := by
    refine hperf.trans ((AddSubgroup.closure_le S).2 ?_)
    rintro y ⟨b, z, hz, rfl⟩
    obtain ⟨δ, hδ⟩ := QuotientAddGroup.mk_surjective (π ⟨z, hz⟩)
    have hζN : z - F (δ : Fin 7 → ZMod 2) ∈ N := N.sub_mem hz (hFN _)
    have hπζ : π ⟨z - F (δ : Fin 7 → ZMod 2), hζN⟩ = 0 := by
      have e : (⟨z - F (δ : Fin 7 → ZMod 2), hζN⟩ : ↥N) =
          ⟨z, hz⟩ - ⟨F (δ : Fin 7 → ZMod 2), hFN _⟩ := rfl
      rw [e, map_sub, hπF δ, hδ, sub_self]
    have hρζ : ρ b (z - F (δ : Fin 7 → ZMod 2)) = z - F (δ : Fin 7 → ZMod 2) :=
      hπk ⟨z - F (δ : Fin 7 → ZMod 2), hζN⟩ hπζ b
    rw [map_sub] at hρζ
    refine AddSubgroup.mem_map.2 ⟨fun k => (δ : Fin 7 → ZMod 2) ((b : Perm (Fin 7))⁻¹ k) -
      (δ : Fin 7 → ZMod 2) k, ?_, ?_⟩
    · rw [mem_evenWeight_iff]
      have h5 := Equiv.sum_comp ((b : Perm (Fin 7))⁻¹) (δ : Fin 7 → ZMod 2)
      exact (Finset.sum_sub_distrib _ _).trans (sub_eq_zero.2 h5)
    · calc F (fun k => (δ : Fin 7 → ZMod 2) ((b : Perm (Fin 7))⁻¹ k) - (δ : Fin 7 → ZMod 2) k)
          = F (fun k => (δ : Fin 7 → ZMod 2) ((b : Perm (Fin 7))⁻¹ k)) -
            F (δ : Fin 7 → ZMod 2) := by rw [← map_sub]; rfl
        _ = ρ b (F (δ : Fin 7 → ZMod 2)) - F (δ : Fin 7 → ZMod 2) := by rw [hFρ]
        _ = ρ b z - z := (sub_eq_sub_iff_sub_eq_sub.1 hρζ).symm
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨δ, hδ, hFδ⟩ := AddSubgroup.mem_map.1 (hNS x.2)
  have hδ' : π x = QuotientAddGroup.mk ⟨δ, hδ⟩ := by
    have : x = ⟨F δ, hFN δ⟩ := Subtype.ext hFδ.symm
    rw [this]
    exact hπF ⟨δ, hδ⟩
  rw [hδ'] at hx
  have h1 : (⟨δ, hδ⟩ : evenWeight 7) ∈ evenWeightOnes 7 := (QuotientAddGroup.eq_zero_iff _).1 hx
  rw [CFSG.RankThree.PartTwo.Sec19.Item194Proof.evenWeightOnes_eq_bot (⟨3, rfl⟩ : Odd 7)] at h1
  have h2 : (⟨δ, hδ⟩ : evenWeight 7) = 0 := AddSubgroup.mem_bot.1 h1
  have hδ0 : δ = 0 := congrArg Subtype.val h2
  apply Subtype.ext
  rw [← hFδ, hδ0, map_zero]
  rfl

end Split

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
