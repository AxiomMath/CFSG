module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM

variable {n : ℕ}

namespace RootFourAux

section PermFacts

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem perm_inv_apply_self (σ : Equiv.Perm α) (x : α) : σ⁻¹ (σ x) = x := σ.symm_apply_apply x

theorem perm_apply_inv_self (σ : Equiv.Perm α) (x : α) : σ (σ⁻¹ x) = x := σ.apply_symm_apply x

theorem card_support_eq_two_mul {σ : Equiv.Perm α} (h2 : σ ^ 2 = 1) :
    σ.support.card = 2 * Multiset.card σ.cycleType := by
  have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) h2
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  omega

theorem card_support_eq_four {σ : Equiv.Perm α} (h2 : σ ^ 2 = 1) (hs : Equiv.Perm.sign σ = 1)
    (h1 : σ ≠ 1) (h4 : σ.support.card ≤ 4) : σ.support.card = 4 := by
  have hc := card_support_eq_two_mul h2
  have hc0 : Multiset.card σ.cycleType ≠ 0 := fun h =>
    h1 (Equiv.Perm.card_cycleType_eq_zero.mp h)
  have hsign := Equiv.Perm.sign_of_cycleType σ
  rw [hs, Equiv.Perm.sum_cycleType, hc] at hsign
  have hev : Even (Multiset.card σ.cycleType) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hodd' : Odd (2 * Multiset.card σ.cycleType + Multiset.card σ.cycleType) :=
      (even_two_mul _).add_odd hodd
    rw [hodd'.neg_one_pow] at hsign
    exact absurd hsign (by decide)
  obtain ⟨r, hr⟩ := hev
  omega

theorem cycleType_eq_of_card_support {σ : Equiv.Perm α} (h2 : σ ^ 2 = 1)
    (h4 : σ.support.card = 4) : σ.cycleType = Multiset.replicate 2 2 := by
  have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) h2
  have hc := card_support_eq_two_mul h2
  have h2c : Multiset.card σ.cycleType = 2 := by omega
  rw [hrep, h2c]

end PermFacts

theorem exists_fix_even (hn : 6 ≤ n) {S : Finset (Fin n)} (hS : S.card ≤ 4)
    (τ : Equiv.Perm (Fin n)) :
    ∃ ρ : Equiv.Perm (Fin n), (∀ i ∈ S, ρ i = i) ∧ Equiv.Perm.sign (ρ * τ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
  · exact ⟨1, fun _ _ => rfl, by simpa using h⟩
  · have hlt : 1 < Sᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hlt
    refine ⟨Equiv.swap p q, fun i hi => ?_, ?_⟩
    · exact Equiv.swap_apply_of_ne_of_ne
        (fun h => (Finset.mem_compl.mp hp) (h ▸ hi))
        (fun h => (Finset.mem_compl.mp hq) (h ▸ hi))
    · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hpq, h]
      decide

section RootFour

variable {V : Subgroup ↥(alternatingGroup (Fin n))}

noncomputable def movedOf (V : Subgroup ↥(alternatingGroup (Fin n))) : Finset (Fin n) :=
  open Classical in
  Finset.univ.filter fun i => ¬ ∀ v ∈ V, (v : Equiv.Perm (Fin n)) i = i

theorem mem_movedOf {i : Fin n} :
    i ∈ movedOf V ↔ ¬ ∀ v ∈ V, (v : Equiv.Perm (Fin n)) i = i := by
  simp [movedOf]

theorem card_movedOf (h : IsRootFour V) : (movedOf V).card = 4 := by
  classical
  have h3 := h.2.2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h3
  unfold movedOf
  convert h3

theorem pow_two_eq_one (h : IsRootFour V) {v : ↥(alternatingGroup (Fin n))} (hv : v ∈ V) :
    (v : Equiv.Perm (Fin n)) ^ 2 = 1 := by
  have := h.2.1 v hv
  exact congrArg Subtype.val this

theorem support_subset_movedOf {v : ↥(alternatingGroup (Fin n))} (hv : v ∈ V) :
    (v : Equiv.Perm (Fin n)).support ⊆ movedOf V := by
  intro i hi
  rw [Equiv.Perm.mem_support] at hi
  rw [mem_movedOf]
  intro hall
  exact hi (hall v hv)

theorem apply_eq_of_notMem_movedOf {v : ↥(alternatingGroup (Fin n))} (hv : v ∈ V) {i : Fin n}
    (hi : i ∉ movedOf V) : (v : Equiv.Perm (Fin n)) i = i := by
  by_contra hne
  exact hi (support_subset_movedOf hv (Equiv.Perm.mem_support.mpr hne))

end RootFour

end RootFourAux

theorem rootFour_support_card {V₄ : Subgroup ↥(alternatingGroup (Fin n))} (h : IsRootFour V₄)
    {v : ↥(alternatingGroup (Fin n))} (hv : v ∈ V₄) (hv1 : v ≠ 1) :
    (v : Equiv.Perm (Fin n)) ^ 2 = 1 ∧ (v : Equiv.Perm (Fin n)).support.card = 4 := by
  have h2 := RootFourAux.pow_two_eq_one h hv
  refine ⟨h2, RootFourAux.card_support_eq_four h2 (Equiv.Perm.mem_alternatingGroup.mp v.2)
    (fun h1 => hv1 (Subtype.ext h1)) ?_⟩
  calc (v : Equiv.Perm (Fin n)).support.card ≤ (RootFourAux.movedOf V₄).card :=
        Finset.card_le_card (RootFourAux.support_subset_movedOf hv)
    _ = 4 := RootFourAux.card_movedOf h

namespace RootFourAux

variable {V : Subgroup ↥(alternatingGroup (Fin n))}

theorem apply_mem_movedOf {m : Fin n} (hm : m ∈ movedOf V) {w : ↥(alternatingGroup (Fin n))}
    (hw : w ∈ V) : (w : Equiv.Perm (Fin n)) m ∈ movedOf V := by
  rw [mem_movedOf] at hm ⊢
  intro hall
  apply hm
  intro u hu
  have h1 : (w : Equiv.Perm (Fin n)) m = m := by
    have := hall w⁻¹ (V.inv_mem hw)
    simp at this
    exact this.symm
  have h2 := hall u hu
  rwa [h1] at h2

theorem eq_of_apply_eq (h : IsRootFour V) {m : Fin n} (hm : m ∈ movedOf V)
    {v w : ↥(alternatingGroup (Fin n))} (hv : v ∈ V) (hw : w ∈ V)
    (hvw : (v : Equiv.Perm (Fin n)) m = (w : Equiv.Perm (Fin n)) m) : v = w := by
  by_contra hne
  have hu : w⁻¹ * v ∈ V := V.mul_mem (V.inv_mem hw) hv
  have hu1 : w⁻¹ * v ≠ 1 := fun h1 => hne (inv_mul_eq_one.mp h1).symm
  have hsupp : ((w⁻¹ * v : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)).support =
      movedOf V := by
    apply Finset.eq_of_subset_of_card_le (support_subset_movedOf hu)
    rw [card_movedOf h, (rootFour_support_card h hu hu1).2]
  have hmem : m ∈ ((w⁻¹ * v : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)).support :=
    hsupp ▸ hm
  rw [Equiv.Perm.mem_support] at hmem
  apply hmem
  show (w : Equiv.Perm (Fin n))⁻¹ ((v : Equiv.Perm (Fin n)) m) = m
  rw [hvw]
  simp

theorem exists_apply_eq (h : IsRootFour V) {m : Fin n} (hm : m ∈ movedOf V) {y : Fin n}
    (hy : y ∈ movedOf V) : ∃ w ∈ V, (w : Equiv.Perm (Fin n)) m = y := by
  classical
  haveI : Fintype ↥V := Fintype.ofFinite _
  have hinj : Function.Injective
      (fun w : ↥V => ((w : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) m) :=
    fun a b hab => Subtype.ext (eq_of_apply_eq h hm a.2 b.2 hab)
  have hF : (Finset.univ.image
      fun w : ↥V => ((w : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) m) =
      movedOf V := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hi
      exact apply_mem_movedOf hm w.2
    · rw [card_movedOf h, Finset.card_image_of_injective _ hinj, Finset.card_univ,
        ← Nat.card_eq_fintype_card, h.1]
  rw [← hF] at hy
  obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hy
  exact ⟨w, w.2, hw⟩

theorem nonempty_mulEquiv {V' : Subgroup ↥(alternatingGroup (Fin n))} (h : IsRootFour V)
    (h' : IsRootFour V') : Nonempty (↥V ≃* ↥V') := by
  have key : ∀ {W : Subgroup ↥(alternatingGroup (Fin n))}, IsRootFour W →
      Nonempty (↥W ≃* Multiplicative (Fin 2 → ZMod 2)) := by
    intro W hW
    have hpow : ∀ a : ↥W, a ^ 2 = 1 := fun a => Subtype.ext (hW.2.1 a a.2)
    have hcomm : ∀ a b : ↥W, a * b = b * a := by
      intro a b
      have ha : a * a = 1 := by rw [← sq]; exact hpow a
      have hb : b * b = 1 := by rw [← sq]; exact hpow b
      have hab : (a * b) * (a * b) = 1 := by rw [← sq]; exact hpow (a * b)
      calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
    exact CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hpow
      (by rw [hW.1]; norm_num)
  obtain ⟨e⟩ := key h
  obtain ⟨e'⟩ := key h'
  exact ⟨e.trans e'.symm⟩

end RootFourAux

theorem rootFour_conj (hn : 6 ≤ n) {V₄ V₄' : Subgroup ↥(alternatingGroup (Fin n))}
    (h : IsRootFour V₄) (h' : IsRootFour V₄') :
    ∃ x : ↥(alternatingGroup (Fin n)), V₄.map (MulAut.conj x).toMonoidHom = V₄' := by
  classical
  obtain ⟨m, hm⟩ : (RootFourAux.movedOf V₄).Nonempty :=
    Finset.card_pos.mp (by rw [RootFourAux.card_movedOf h]; norm_num)
  obtain ⟨m', hm'⟩ : (RootFourAux.movedOf V₄').Nonempty :=
    Finset.card_pos.mp (by rw [RootFourAux.card_movedOf h']; norm_num)
  obtain ⟨θ⟩ := RootFourAux.nonempty_mulEquiv h h'
  obtain ⟨f, hfdef⟩ : ∃ f : ↥V₄ → Fin n, ∀ w : ↥V₄,
      f w = ((w : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) m := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ↥V₄ → Fin n, ∀ w : ↥V₄,
      g w = (((θ w : ↥V₄') : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) m' :=
    ⟨_, fun _ => rfl⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (RootFourAux.eq_of_apply_eq h hm a.2 b.2 (by rwa [hfdef, hfdef] at hab))
  have hg : Function.Injective g := fun a b hab =>
    θ.injective (Subtype.ext
      (RootFourAux.eq_of_apply_eq h' hm' (θ a).2 (θ b).2 (by rwa [hgdef, hgdef] at hab)))
  obtain ⟨σ₀, hσ₀⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  obtain ⟨ρ, hρ, hsgn⟩ := RootFourAux.exists_fix_even hn (S := RootFourAux.movedOf V₄')
    (by rw [RootFourAux.card_movedOf h']) σ₀
  obtain ⟨σ, hsgn', hσ⟩ : ∃ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = 1 ∧
      ∀ w : ↥V₄, σ (f w) = g w :=
    ⟨ρ * σ₀, hsgn, fun w => by
      rw [Equiv.Perm.mul_apply, hσ₀ w]
      exact hρ _ (by rw [hgdef]; exact RootFourAux.apply_mem_movedOf hm' (θ w).2)⟩
  have key : ∀ a : ↥V₄, σ * ((a : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) * σ⁻¹ =
      (((θ a : ↥V₄') : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) := by
    intro a
    ext y
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    by_cases hy : y ∈ RootFourAux.movedOf V₄'
    · obtain ⟨u, hu, hum⟩ := RootFourAux.exists_apply_eq h' hm' hy
      obtain ⟨b, hb⟩ := θ.surjective ⟨u, hu⟩
      have hyb : y = σ (f b) := by
        rw [hσ b, hgdef b, hb]
        exact hum.symm
      rw [hyb, RootFourAux.perm_inv_apply_self]
      have h1 : ((a : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n)) (f b) = f (a * b) := by
        rw [hfdef, hfdef]
        rfl
      rw [h1, hσ (a * b), hσ b, hgdef, hgdef, map_mul]
      rfl
    · have hσy : σ⁻¹ y ∉ RootFourAux.movedOf V₄ := by
        intro hmem
        obtain ⟨w, hw, hwm⟩ := RootFourAux.exists_apply_eq h hm hmem
        apply hy
        have hfw : f ⟨w, hw⟩ = σ⁻¹ y := by rw [hfdef]; exact hwm
        have hyw : y = g ⟨w, hw⟩ := by
          rw [← hσ, hfw, RootFourAux.perm_apply_inv_self]
        rw [hyw, hgdef]
        exact RootFourAux.apply_mem_movedOf hm' (θ _).2
      rw [RootFourAux.apply_eq_of_notMem_movedOf a.2 hσy, RootFourAux.perm_apply_inv_self,
        RootFourAux.apply_eq_of_notMem_movedOf (θ a).2 hy]
  obtain ⟨x, hx⟩ : ∃ x : ↥(alternatingGroup (Fin n)), (x : Equiv.Perm (Fin n)) = σ :=
    ⟨⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hsgn'⟩, rfl⟩
  refine ⟨x, ?_⟩
  have hle : V₄.map (MulAut.conj x).toMonoidHom ≤ V₄' := by
    rintro _ ⟨v, hv, rfl⟩
    have hk : x * v * x⁻¹ = ((θ ⟨v, hv⟩ : ↥V₄') : ↥(alternatingGroup (Fin n))) := by
      apply Subtype.ext
      show (x : Equiv.Perm (Fin n)) * (v : Equiv.Perm (Fin n)) * (x : Equiv.Perm (Fin n))⁻¹ = _
      rw [hx]
      exact key ⟨v, hv⟩
    show x * v * x⁻¹ ∈ V₄'
    rw [hk]
    exact (θ ⟨v, hv⟩).2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [h'.1, Subgroup.card_map_of_injective (MulAut.conj x).injective, h.1]

theorem rootFour_elem_conj (hn : 6 ≤ n) {V₄ V₄' : Subgroup ↥(alternatingGroup (Fin n))}
    (h : IsRootFour V₄) (h' : IsRootFour V₄') {v v' : ↥(alternatingGroup (Fin n))}
    (hv : v ∈ V₄) (hv1 : v ≠ 1) (hv' : v' ∈ V₄') (hv1' : v' ≠ 1) :
    ∃ x : ↥(alternatingGroup (Fin n)), x * v * x⁻¹ = v' := by
  obtain ⟨h2, hc⟩ := rootFour_support_card h hv hv1
  obtain ⟨h2', hc'⟩ := rootFour_support_card h' hv' hv1'
  have hconj : IsConj (v : Equiv.Perm (Fin n)) (v' : Equiv.Perm (Fin n)) := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq, RootFourAux.cycleType_eq_of_card_support h2 hc,
      RootFourAux.cycleType_eq_of_card_support h2' hc']
  obtain ⟨x₀, hx₀⟩ := isConj_iff.mp hconj
  obtain ⟨ρ, hρ, hsgn⟩ := RootFourAux.exists_fix_even hn
    (S := (v' : Equiv.Perm (Fin n)).support) hc'.le x₀
  refine ⟨⟨ρ * x₀, Equiv.Perm.mem_alternatingGroup.mpr hsgn⟩, Subtype.ext ?_⟩
  have hdisj : Equiv.Perm.Disjoint ρ (v' : Equiv.Perm (Fin n)) := by
    intro i
    by_cases hi : i ∈ (v' : Equiv.Perm (Fin n)).support
    · exact Or.inl (hρ i hi)
    · exact Or.inr (Equiv.Perm.notMem_support.mp hi)
  show ρ * x₀ * (v : Equiv.Perm (Fin n)) * (ρ * x₀)⁻¹ = v'
  calc ρ * x₀ * (v : Equiv.Perm (Fin n)) * (ρ * x₀)⁻¹
      = ρ * (x₀ * (v : Equiv.Perm (Fin n)) * x₀⁻¹) * ρ⁻¹ := by group
    _ = ρ * (v' : Equiv.Perm (Fin n)) * ρ⁻¹ := by rw [hx₀]
    _ = v' := by rw [hdisj.commute.eq, mul_inv_cancel_right]

theorem exists_zpowers_of_card_two {G : Type*} [Group G] {H : Subgroup G} (hc : Nat.card ↥H = 2) :
    ∃ v ∈ H, v ≠ 1 ∧ H = Subgroup.zpowers v := by
  have hfin : Finite ↥H := Nat.finite_of_card_ne_zero (by omega)
  have hnt : Nontrivial ↥H := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥H)
  refine ⟨x, x.2, fun h => hx (Subtype.ext h), ?_⟩
  have hord : orderOf (x : G) = 2 := by
    have hdvd : orderOf x ∣ 2 := hc ▸ orderOf_dvd_natCard x
    have hne : orderOf x ≠ 1 := fun h1 => hx (orderOf_eq_one_iff.mp h1)
    have h2 : orderOf x = 2 := ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left hne
    rw [← h2]
    exact Subgroup.orderOf_coe x
  have hle : Subgroup.zpowers (x : G) ≤ H := Subgroup.zpowers_le.mpr x.2
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hc, Nat.card_zpowers, hord]

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.LayerM
