module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor

open CFSG.Open CFSG.OrderReductions.InvariantSylow

theorem lift_torus {H M : Type} [Group H] [Finite H] [Group M] [Finite M]
    (π : H →* M) (hsurj : Function.Surjective π) (hker : ¬ 3 ∣ Nat.card π.ker)
    (E0 U : Subgroup M) (hE0 : IsPGroup 3 E0) (hE0ab : IsElemAbelian 3 E0)
    (hE0c : Nat.card E0 = 9) (hU : IsPGroup 2 U) (x₀ : M) (hx₀U : x₀ ∈ U) (hx₀ : x₀ ≠ 1)
    (hx₀2 : x₀ ^ 2 = 1) (hnorm : ∀ e ∈ E0, e ∈ Subgroup.normalizer (U : Set M)) :
    ∃ W : Subgroup H, IsPGroup 3 W ∧ IsElemAbelian 3 W ∧ Nat.card W = 9 ∧
      ∃ T : Subgroup H, IsPGroup 2 T ∧ (∀ w ∈ W, w ∈ Subgroup.normalizer (T : Set H)) ∧
        ¬ T ≤ π.ker := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEπ : E0 ≤ π.range := by
    rw [MonoidHom.range_eq_top.2 hsurj]
    exact le_top
  obtain ⟨W, hW3, hWmap, hWinj⟩ := exists_pSubgroup_lift Nat.prime_three π hker hE0 hEπ
  let T₁ : Subgroup H := U.comap π
  have hker_le : π.ker ≤ T₁ := by
    intro x hx
    show π x ∈ U
    rw [MonoidHom.mem_ker.1 hx]
    exact U.one_mem
  have hWnorm : ∀ w ∈ W, w ∈ Subgroup.normalizer (T₁ : Set H) := by
    intro w hw
    have hπw : π w ∈ E0 := by
      rw [← hWmap]
      exact ⟨w, hw, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    show π h ∈ U ↔ π (w * h * w⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 (hnorm (π w) hπw) (π h)
  let g : T₁ →* M := π.comp T₁.subtype
  have hgrange : g.range = U := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hu
      obtain ⟨x, hx⟩ := hsurj u
      exact ⟨⟨x, by show π x ∈ U; rw [hx]; exact hu⟩, hx⟩
  have hgker : g.ker = π.ker.subgroupOf T₁ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rfl
  have hcardT₁ : Nat.card T₁ = Nat.card π.ker * Nat.card U := by
    have h1 := Subgroup.card_mul_index g.ker
    have h2 : Nat.card g.ker = Nat.card π.ker := by
      rw [hgker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
    have h3 : g.ker.index = Nat.card U := by
      rw [Subgroup.index_ker, hgrange]
    rw [h2, h3] at h1
    exact h1.symm
  have hU3 : ¬ 3 ∣ Nat.card U := by
    obtain ⟨n, hn⟩ := hU.exists_card_eq
    intro h3
    rw [hn] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at this
  have hcop : ¬ 3 ∣ Nat.card T₁ := by
    rw [hcardT₁]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h1 | h1
    · exact hker h1
    · exact hU3 h1
  have hinv : ∀ w : W, T₁.map
      (((MulAut.conj : H →* MulAut H).comp W.subtype) w).toMonoidHom = T₁ := by
    intro w
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [← hyx]
      exact (Subgroup.mem_normalizer_iff.1 (hWnorm w w.2) y).1 hy
    · intro hx
      refine ⟨(w : H)⁻¹ * x * (w : H), ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hWnorm w w.2) _).2 (by
          simpa [mul_assoc] using hx)
      · simp [mul_assoc]
  obtain ⟨S₀, hS₀⟩ := exists_invariant_sylow_of_coprime (actor := W) (group := T₁) 3 2 hW3 hcop
    (restrictedHomomorphism ((MulAut.conj : H →* MulAut H).comp W.subtype) T₁ hinv)
  set c := restrictedHomomorphism ((MulAut.conj : H →* MulAut H).comp W.subtype) T₁ hinv with hc
  have hact : ∀ (w : W) (t : T₁), T₁.subtype (c w t) = (w : H) * T₁.subtype t * (w : H)⁻¹ :=
    fun w t => rfl
  let T : Subgroup H := (S₀ : Subgroup T₁).map T₁.subtype
  have hT2 : IsPGroup 2 T := (S₀.isPGroup').map T₁.subtype
  have hTnorm : ∀ w ∈ W, w ∈ Subgroup.normalizer (T : Set H) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hcs : c ⟨w, hw⟩ s ∈ (S₀ : Subgroup T₁).map (c ⟨w, hw⟩).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hs
      rw [hS₀ ⟨w, hw⟩] at hcs
      exact ⟨c ⟨w, hw⟩ s, hcs, hact ⟨w, hw⟩ s⟩
    · rintro ⟨s, hs, hsh⟩
      have hs' : s ∈ (S₀ : Subgroup T₁).map (c ⟨w, hw⟩).toMonoidHom := by
        rw [hS₀ ⟨w, hw⟩]
        exact hs
      obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.1 hs'
      refine ⟨t, ht, ?_⟩
      have h2 : (w : H) * T₁.subtype t * (w : H)⁻¹ = (w : H) * h * (w : H)⁻¹ := by
        rw [← hact ⟨w, hw⟩ t]
        have hts' : c ⟨w, hw⟩ t = s := hts
        rw [hts', hsh]
      have h3 := congrArg (fun y => (w : H)⁻¹ * y * (w : H)) h2
      simpa [mul_assoc] using h3
  have hTnot : ¬ T ≤ π.ker := by
    intro hTk
    have hSle : (S₀ : Subgroup T₁) ≤ g.ker := by
      intro s hs
      have hk := hTk (Subgroup.mem_map_of_mem _ hs)
      exact hk
    have hdvd : g.ker.index ∣ (S₀ : Subgroup T₁).index := Subgroup.index_dvd_of_le hSle
    have hg_index : g.ker.index = Nat.card U := by
      rw [Subgroup.index_ker, hgrange]
    have h2U : 2 ∣ Nat.card U := by
      have hx : (⟨x₀, hx₀U⟩ : U) ≠ 1 := by
        intro h
        exact hx₀ (congrArg Subtype.val h)
      have hx2 : (⟨x₀, hx₀U⟩ : U) ^ 2 = 1 := Subtype.ext hx₀2
      have hord : orderOf (⟨x₀, hx₀U⟩ : U) = 2 := orderOf_eq_prime hx2 hx
      have hdiv := orderOf_dvd_natCard (⟨x₀, hx₀U⟩ : U)
      rwa [hord] at hdiv
    rw [hg_index] at hdvd
    exact Sylow.not_dvd_index S₀ (dvd_trans h2U hdvd)
  have hWcard : Nat.card W = 9 := by
    rw [card_eq_of_injective_comp_subtype π hWinj, hWmap, hE0c]
  have hmemE : ∀ x ∈ W, π x ∈ E0 := fun x hx => by
    rw [← hWmap]
    exact ⟨x, hx, rfl⟩
  have hWab : IsElemAbelian 3 W := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · apply hWinj
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, Subgroup.coe_mul]
      have hca := hmemE a a.2
      have hcb := hmemE b b.2
      have := hE0ab.1.is_comm.comm ⟨π a, hca⟩ ⟨π b, hcb⟩
      exact congrArg Subtype.val this
    · intro x hx
      have hx3 : (⟨x, hx⟩ : W) ^ 3 = 1 := by
        apply hWinj
        rw [map_pow, map_one]
        have := hE0ab.2 (π x) (hmemE x hx)
        exact this
      exact congrArg Subtype.val hx3
  exact ⟨W, hW3, hWab, hWcard, T, hT2, hTnorm, hTnot⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor
