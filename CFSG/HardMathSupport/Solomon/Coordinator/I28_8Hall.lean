module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallExistence
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8

open CFSG.SignalizerFunctor.Helpers CFSG.HardMathSupport.Solomon.UniquenessMaximal

theorem exists_hall_two_seven {G : Type} [Group G] [Finite G] [Group.IsSolvable G]
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hT : ¬ 2 ∣ T.index) :
    ∃ R : Subgroup G, T ≤ R ∧ (∀ p : ℕ, p.Prime → p ∣ Nat.card R → p = 2 ∨ p = 7) ∧
      ∀ p : ℕ, p.Prime → p ∣ R.index → p ≠ 2 ∧ p ≠ 7 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hHc, hHi⟩ := solvable_hall_subgroup_exists G ({2, 7} : Set ℕ)
  let T' : Sylow 2 G := hT2.toSylow hT
  obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
  have hS'2 : IsPGroup 2 ((S : Subgroup H).map H.subtype) := S.isPGroup'.map H.subtype
  have hS'idx : ¬ 2 ∣ ((S : Subgroup H).map H.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
    · exact S.not_dvd_index h
    · have := hHi 2 Nat.prime_two h
      simp at this
  let S'' : Sylow 2 G := hS'2.toSylow hS'idx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S'' T'
  refine ⟨H.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ ((g • S'' : Sylow 2 G) : Subgroup G) := by rw [hg]; exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
    obtain ⟨h', hh', hh'e⟩ := hx'
    refine ⟨h', h'.2, ?_⟩
    have h1 : (h' : G) = (MulAut.conj g)⁻¹ • x := hh'e
    rw [h1]
    simp [MulAut.smul_def]
    group
  · intro p hp hpd
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hpd
    exact hHc p hp hpd
  · intro p hp hpd
    rw [Subgroup.index_map_of_bijective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).bijective H] at hpd
    have := hHi p hp hpd
    simp at this
    exact this

theorem sup_two_seven {Y : Type} [Group Y] [Finite Y] {A Q : Subgroup Y} (hA : IsPGroup 2 A)
    (hQ : Nat.card Q = 7) (hAQ : A ≤ Subgroup.normalizer (Q : Set Y)) :
    Group.IsSolvable ↥(A ⊔ Q) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(A ⊔ Q) → p = 2 ∨ p = 7) ∧
      ¬ 2 ∣ A.relIndex (A ⊔ Q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set H : Subgroup Y := A ⊔ Q with hH
  have hle : H ≤ Subgroup.normalizer (Q : Set Y) :=
    sup_le hAQ (Subgroup.le_normalizer)
  have hnorm : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hle
  set Q' : Subgroup H := Q.subgroupOf H with hQ'
  set A' : Subgroup H := A.subgroupOf H with hA'
  have hQ'c : Nat.card Q' = 7 := by
    rw [← hQ]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have htop : A' ⊔ Q' = ⊤ := by
    rw [hA', hQ', ← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self (A ⊔ Q)
  have hidx : Q'.index = Q'.relIndex A' := by
    have := Subgroup.relIndex_sup_right (H := A') (K := Q')
    rwa [htop, Subgroup.relIndex_top_right] at this
  have hA'2 : IsPGroup 2 A' := hA.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_left).symm
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hA'2
  have hrel : Q'.relIndex A' ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card Q' A'
  have hcardH : Nat.card H = Q'.index * 7 := by
    rw [← hQ'c, mul_comm, ← Subgroup.card_mul_index Q']
  refine ⟨?_, ?_, ?_⟩
  · have hq : Group.IsSolvable Q' := by
      have : IsCyclic Q' := isCyclic_of_prime_card hQ'c
      infer_instance
    have hquot : Group.IsSolvable (H ⧸ Q') := by
      have hp : IsPGroup 2 (H ⧸ Q') := by
        have hsurj : Function.Surjective ((QuotientGroup.mk' Q').comp A'.subtype) := by
          intro y
          obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
          have : h ∈ A' ⊔ Q' := htop ▸ Subgroup.mem_top h
          obtain ⟨a, ha, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 this
          exact ⟨⟨a, ha⟩, QuotientGroup.eq.2 (by simpa using hq)⟩
        exact hA'2.of_surjective _ hsurj
      have := hp.isNilpotent
      infer_instance
    exact Group.isSolvable_of_ker_le_range Q'.subtype (QuotientGroup.mk' Q') (by
      simp [QuotientGroup.ker_mk'])
  · intro p hp hpd
    rw [hcardH] at hpd
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
    · rw [hidx] at h
      exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (hp.dvd_of_dvd_pow (h.trans hrel)))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)
  · intro h2
    have hi : A.relIndex (A ⊔ Q) = A'.index := rfl
    have h1 : Nat.card H = Nat.card A' * A'.index := (Subgroup.card_mul_index A').symm
    have h3 : Nat.card (Q'.subgroupOf A') * Q'.relIndex A' = Nat.card A' :=
      Subgroup.card_mul_index (Q'.subgroupOf A')
    have hr0 : 0 < Q'.relIndex A' := by
      rw [← hidx]; exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have h4 : Nat.card (Q'.subgroupOf A') * A'.index = 7 := by
      apply Nat.eq_of_mul_eq_mul_left hr0
      calc Q'.relIndex A' * (Nat.card (Q'.subgroupOf A') * A'.index)
          = (Nat.card (Q'.subgroupOf A') * Q'.relIndex A') * A'.index := by ring
        _ = Nat.card H := by rw [h3, ← h1]
        _ = Q'.relIndex A' * 7 := by rw [hcardH, hidx]
    rw [hi] at h2
    have : 2 ∣ 7 := h2.trans ⟨_, h4.symm.trans (mul_comm _ _)⟩
    omega

theorem frattini_ker {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal] {P : Subgroup X}
    (hPN : P ≤ N) (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.relIndex N) :
    Subgroup.normalizer (P : Set X) ⊔ N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf N) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
  let S : Sylow 2 N := hP'.toSylow hidx
  have h := Sylow.normalizer_sup_eq_top S
  have hmap : (S : Subgroup N).map N.subtype = P := by
    change (P.subgroupOf N).map N.subtype = P
    rw [Subgroup.map_subgroupOf_eq_of_le hPN]
  rw [← h, hmap]

theorem relIndex_sup_of_le_normalizer {Y : Type} [Group Y] [Finite Y] {A L : Subgroup Y}
    (hAL : A ≤ Subgroup.normalizer (L : Set Y)) :
    A.relIndex (A ⊔ L) = (A ⊓ L).relIndex L := by
  classical
  set H : Subgroup Y := A ⊔ L with hH
  have hle : H ≤ Subgroup.normalizer (L : Set Y) := sup_le hAL Subgroup.le_normalizer
  have hnorm : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hle
  set L' : Subgroup H := L.subgroupOf H with hL'
  set A' : Subgroup H := A.subgroupOf H with hA'
  have htop : A' ⊔ L' = ⊤ := by
    rw [hA', hL', ← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self (A ⊔ L)
  have hidx : L'.index = L'.relIndex A' := by
    have := Subgroup.relIndex_sup_right (H := A') (K := L')
    rwa [htop, Subgroup.relIndex_top_right] at this
  have h1 : Nat.card H = L'.index * Nat.card L' := (Subgroup.index_mul_card L').symm
  have h2 : Nat.card H = Nat.card A' * A'.index := (Subgroup.card_mul_index A').symm
  have h3 : Nat.card (L'.subgroupOf A') * L'.relIndex A' = Nat.card A' :=
    Subgroup.card_mul_index (L'.subgroupOf A')
  have hr0 : 0 < L'.relIndex A' := by
    rw [← hidx]; exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hL'c : Nat.card L' = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h4 : Nat.card (L'.subgroupOf A') * A'.index = Nat.card L' := by
    apply Nat.eq_of_mul_eq_mul_left hr0
    calc L'.relIndex A' * (Nat.card (L'.subgroupOf A') * A'.index)
        = (Nat.card (L'.subgroupOf A') * L'.relIndex A') * A'.index := by ring
      _ = Nat.card H := by rw [h3, ← h2]
      _ = L'.relIndex A' * Nat.card L' := by rw [h1, hidx]
  have h5 : Nat.card (L'.subgroupOf A') = Nat.card (A ⊓ L : Subgroup Y) := by
    calc Nat.card (L'.subgroupOf A')
        = Nat.card ((L'.subgroupOf A').map A'.subtype) :=
          (Subgroup.card_map_of_injective A'.subtype_injective).symm
      _ = Nat.card (L' ⊓ A' : Subgroup H) := by rw [Subgroup.subgroupOf_map_subtype]
      _ = Nat.card ((L' ⊓ A' : Subgroup H).map H.subtype) :=
          (Subgroup.card_map_of_injective H.subtype_injective).symm
      _ = Nat.card (A ⊓ L : Subgroup Y) := by
          rw [Subgroup.map_inf _ _ H.subtype H.subtype_injective, hL', hA',
            Subgroup.map_subgroupOf_eq_of_le le_sup_right,
            Subgroup.map_subgroupOf_eq_of_le le_sup_left, inf_comm]
  have h6 : Nat.card (A ⊓ L : Subgroup Y) * (A ⊓ L).relIndex L = Nat.card L := by
    have := Subgroup.card_mul_index ((A ⊓ L).subgroupOf L)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ L ≤ L)).toEquiv] at this
  have hpos : 0 < Nat.card (A ⊓ L : Subgroup Y) := Nat.card_pos
  show A'.index = _
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h6, ← hL'c, ← h4, h5]

theorem mem_normalizer_of_conj_mem' {X : Type*} [Group X] {Y : Subgroup X} {g : X}
    (h1 : ∀ x ∈ Y, g * x * g⁻¹ ∈ Y) (h2 : ∀ x ∈ Y, g⁻¹ * x * g ∈ Y) :
    g ∈ Subgroup.normalizer (Y : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem solvable_inf_normalizer {X : Type} [Group X] [Finite X] {N P : Subgroup X}
    (hPN : P ≤ N) (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.relIndex N) :
    Group.IsSolvable ↥(N ⊓ Subgroup.normalizer (P : Set X)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L : Subgroup X := N ⊓ Subgroup.normalizer (P : Set X) with hL
  have hPL : P ≤ L := le_inf hPN Subgroup.le_normalizer
  have hnorm : (P.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPL).2 inf_le_right
  have hP' : IsPGroup 2 (P.subgroupOf L) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
  have hq : Group.IsSolvable (P.subgroupOf L) := by
    have := hP'.isNilpotent
    infer_instance
  have hodd : Odd (Nat.card (↥L ⧸ P.subgroupOf L)) := by
    have h1 : P.relIndex L * L.relIndex N = P.relIndex N :=
      Subgroup.relIndex_mul_relIndex P L N hPL inf_le_left
    have h2 : ¬ 2 ∣ P.relIndex L := fun h => hidx (h.trans ⟨_, h1.symm⟩)
    have h3 : Nat.card (↥L ⧸ P.subgroupOf L) = P.relIndex L := (Subgroup.index_eq_card _).symm
    rw [h3]
    exact Nat.odd_iff.2 (by omega)
  have hqs : Group.IsSolvable (↥L ⧸ P.subgroupOf L) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range (P.subgroupOf L).subtype
    (QuotientGroup.mk' (P.subgroupOf L)) (by simp [QuotientGroup.ker_mk'])

theorem eq_one_of_mem_pgroup_odd {X : Type*} [Group X] {U N' : Subgroup X} (hU2 : IsPGroup 2 U)
    (hodd : ¬ 2 ∣ Nat.card N') {c : X} (hcU : c ∈ U) (hcN : c ∈ N') : c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hU2 ⟨c, hcU⟩
  rw [Subgroup.orderOf_mk] at hj
  have hdvd : orderOf c ∣ Nat.card N' := by
    have := Subgroup.orderOf_dvd_natCard N' hcN
    simpa using this
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simpa using hj
  · exfalso
    apply hodd
    refine (dvd_pow_self 2 hjpos.ne').trans ?_
    rw [← hj]; exact hdvd

theorem two_cover_of_twoSeven (h : Th1FactorizationTwoSeven) {X : Type} [Group X] [Finite X]
    {N : Subgroup X} [hNn : N.Normal] {T U : Subgroup X} (hT2 : IsPGroup 2 T)
    (hPN : ¬ 2 ∣ (T ⊓ N).relIndex N) (hUn : U.Normal) (hU2 : IsPGroup 2 U) (hUT : U ≤ T)
    (hC : Subgroup.centralizer (U : Set X) ≤ U) {D : Type} [Group D] [Finite D] (π : X →* D)
    (hker : π.ker = N) (Q : Subgroup D) (hQ : Nat.card Q = 7) (hQr : Q ≤ π.range)
    (hTQ : T.map π ≤ Subgroup.normalizer (Q : Set D))
    (hinv : ∃ t ∈ T, ∀ q ∈ Q, π t * q * (π t)⁻¹ = q⁻¹) :
    ∃ s : Finset (Fin 3), 2 ≤ s.card ∧ ∀ i ∈ s,
      Q ≤ (Subgroup.normalizer (tripleOf T i : Set X)).map π := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup X := T ⊓ N with hP
  set H : Subgroup D := T.map π ⊔ Q with hH
  set M : Subgroup X := H.comap π with hM
  set M₁ : Subgroup X := M ⊓ Subgroup.normalizer (P : Set X) with hM₁
  have hP2 : IsPGroup 2 P := hT2.to_le inf_le_left
  have hPN' : P ≤ N := inf_le_right
  have hfr := frattini_ker hPN' hP2 hPN
  have hker1 : ∀ n ∈ N, π n = 1 := fun n hn => MonoidHom.mem_ker.1 (hker ▸ hn)
  have hNM : N ≤ M := fun n hn => by
    rw [hM, Subgroup.mem_comap, hker1 n hn]; exact one_mem _
  have hTM : T ≤ M := fun t ht => Subgroup.mem_comap.2 (Subgroup.mem_sup_left ⟨t, ht, rfl⟩)
  have hTnP : T ≤ Subgroup.normalizer (P : Set X) := fun t ht =>
    mem_normalizer_of_conj_mem'
      (fun x hx => ⟨mul_mem (mul_mem ht hx.1) (T.inv_mem ht), hNn.conj_mem x hx.2 t⟩)
      (fun x hx => ⟨mul_mem (mul_mem (T.inv_mem ht) hx.1) ht, by
        simpa using hNn.conj_mem x hx.2 t⁻¹⟩)
  have hTM₁ : T ≤ M₁ := le_inf hTM hTnP
  have hHr : H ≤ π.range := sup_le (by rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩) hQr
  have hπM₁ : M₁.map π = H := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx.1
    · intro y hy
      obtain ⟨x, rfl⟩ := hHr hy
      have hx : x ∈ Subgroup.normalizer (P : Set X) ⊔ N := hfr ▸ Subgroup.mem_top x
      obtain ⟨m, hm, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
      have hπ : π (m * n) = π m := by rw [map_mul, hker1 n hn, mul_one]
      exact ⟨m, ⟨Subgroup.mem_comap.2 (by rw [← hπ]; exact hy), hm⟩, hπ.symm⟩
  obtain ⟨hHsolv, hHprimes, hHodd⟩ := sup_two_seven
    (A := T.map π) (hT2.map π) hQ hTQ
  set L : Subgroup X := N ⊓ Subgroup.normalizer (P : Set X) with hL
  have hLM₁ : L ≤ M₁ := le_inf (inf_le_left.trans hNM) inf_le_right
  have hLsolv : Group.IsSolvable ↥L := solvable_inf_normalizer hPN' hP2 hPN
  have hM₁solv : Group.IsSolvable ↥M₁ := by
    set f : ↥M₁ →* D := π.comp M₁.subtype with hf
    have hrange : f.range = H := by
      rw [← hπM₁]
      ext y
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
    have : Group.IsSolvable ↥f.range := by rw [hrange]; exact hHsolv
    have : Group.IsSolvable ↥(L.subgroupOf M₁) :=
      Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hLM₁).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hLM₁).symm.surjective
    refine Group.isSolvable_of_ker_le_range (L.subgroupOf M₁).subtype f.rangeRestrict ?_
    intro x hx
    have hx1 : π (x : X) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      simpa [hf] using this
    have hxN : (x : X) ∈ N := hker ▸ MonoidHom.mem_ker.2 hx1
    exact ⟨⟨x, ⟨hxN, x.2.2⟩⟩, rfl⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set X) := fun t ht =>
    mem_normalizer_of_conj_mem'
      (fun x hx => ⟨hNn.conj_mem x hx.1 t, by
        have := mul_mem (mul_mem (hTnP ht) hx.2) (Subgroup.inv_mem _ (hTnP ht))
        exact this⟩)
      (fun x hx => ⟨by simpa using hNn.conj_mem x hx.1 t⁻¹, by
        have := mul_mem (mul_mem (Subgroup.inv_mem _ (hTnP ht)) hx.2) (hTnP ht)
        exact this⟩)
  have hTinfL : T ⊓ L = P := by
    ext x
    constructor
    · rintro ⟨hxT, hxN, -⟩; exact ⟨hxT, hxN⟩
    · rintro ⟨hxT, hxN⟩; exact ⟨hxT, hxN, hTnP hxT⟩
  have hPL : P ≤ L := le_inf hPN' Subgroup.le_normalizer
  have hoddPL : ¬ 2 ∣ P.relIndex L := by
    have h1 : P.relIndex L * L.relIndex N = P.relIndex N :=
      Subgroup.relIndex_mul_relIndex P L N hPL inf_le_left
    exact fun h2 => hPN (h2.trans ⟨_, h1.symm⟩)
  have hodd1 : ¬ 2 ∣ T.relIndex (T ⊔ L) := by
    rw [relIndex_sup_of_le_normalizer hTL, hTinfL]; exact hoddPL
  have hsupeq : T ⊔ L = (T.map π).comap π ⊓ M₁ := by
    apply le_antisymm
    · refine sup_le (le_inf (fun t ht => Subgroup.mem_comap.2 ⟨t, ht, rfl⟩) hTM₁)
        (le_inf (fun l hl => Subgroup.mem_comap.2 (by rw [hker1 l hl.1]; exact one_mem _)) hLM₁)
    · rintro x ⟨hx1, hx2⟩
      obtain ⟨t, ht, hte⟩ := Subgroup.mem_comap.1 hx1
      have hl : t⁻¹ * x ∈ L := by
        refine ⟨?_, ?_⟩
        · have h0 : π (t⁻¹ * x) = 1 := by rw [map_mul, map_inv, hte, inv_mul_cancel]
          exact hker ▸ MonoidHom.mem_ker.2 h0
        · exact mul_mem (Subgroup.inv_mem _ (hTnP ht)) hx2.2
      have : x = t * (t⁻¹ * x) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hl)
  have hodd2 : ¬ 2 ∣ (T ⊔ L).relIndex M₁ := by
    rw [hsupeq, Subgroup.inf_relIndex_right, Subgroup.relIndex_comap, hπM₁]
    exact hHodd
  have hoddT : ¬ 2 ∣ T.relIndex M₁ := by
    have h1 := Subgroup.relIndex_mul_relIndex T (T ⊔ L) M₁ le_sup_left (sup_le hTM₁ hLM₁)
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 (h1 ▸ h2) with h3 | h3
    · exact hodd1 h3
    · exact hodd2 h3
  have hT0 : IsPGroup 2 (T.subgroupOf M₁) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTM₁).symm
  have := hM₁solv
  obtain ⟨R₀, hTR₀, hR₀c, hR₀i⟩ := exists_hall_two_seven (G := ↥M₁) hT0 hoddT
  set R : Subgroup X := R₀.map M₁.subtype with hR
  have hRM₁ : R ≤ M₁ := Subgroup.map_subtype_le R₀
  have hTR : T ≤ R := fun t ht => ⟨⟨t, hTM₁ ht⟩, hTR₀ (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hRsolv : Group.IsSolvable ↥R :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hRM₁)
      (Subgroup.inclusion_injective hRM₁)
  have hRprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card R → p = 2 ∨ p = 7 := fun p hp hpd =>
    hR₀c p hp (by rwa [hR, Subgroup.card_map_of_injective M₁.subtype_injective] at hpd)
  have hO : ∀ N' : Subgroup X, N' ≤ R → R ≤ Subgroup.normalizer (N' : Set X) →
      ¬ 2 ∣ Nat.card N' → N' = ⊥ := by
    intro N' hN'R hRN' hodd
    rw [eq_bot_iff]
    intro n hn
    have hnC : n ∈ Subgroup.centralizer (U : Set X) := by
      intro u hu
      have huR : u ∈ R := hTR (hUT hu)
      have hc1 : n * u * n⁻¹ * u⁻¹ ∈ U := mul_mem (hUn.conj_mem u hu n) (U.inv_mem hu)
      have hc2 : n * u * n⁻¹ * u⁻¹ ∈ N' := by
        have := mul_mem hn ((Subgroup.mem_normalizer_iff.1 (hRN' huR) n⁻¹).1 (N'.inv_mem hn))
        simpa [mul_assoc] using this
      have hc := eq_one_of_mem_pgroup_odd hU2 hodd hc1 hc2
      have : u * n = n * u := by
        have h3 : n * u * n⁻¹ * u⁻¹ = 1 := hc
        calc u * n = (n * u * n⁻¹ * u⁻¹)⁻¹ * (n * u) := by group
          _ = n * u := by rw [h3]; simp
      exact this
    exact Subgroup.mem_bot.2 (eq_one_of_mem_pgroup_odd hU2 hodd (hC hnC) hn)
  have hSyl : ¬ 2 ∣ T.relIndex R := by
    have h1 := Subgroup.relIndex_mul_relIndex T R M₁ hTR hRM₁
    exact fun h2 => hoddT (h1 ▸ Dvd.dvd.mul_right h2 _)
  have hRmap : R.map π = T.map π ⊔ Q := by
    apply le_antisymm
    · exact (Subgroup.map_mono hRM₁).trans hπM₁.le
    · let f : ↥M₁ →* ↥H := (π.comp M₁.subtype).codRestrict H (fun x => x.2.1)
      have hfs : Function.Surjective f := by
        rintro ⟨y, hy⟩
        rw [← hπM₁] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨⟨x, hx⟩, rfl⟩
      have hdvd := Subgroup.index_map_dvd (H := R₀) hfs
      have hdvd2 : (R₀.map f).index ∣ Nat.card H := Subgroup.index_dvd_card _
      have hone : (R₀.map f).index = 1 := by
        by_contra hne
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
        have h1 := hR₀i p hp (hpd.trans hdvd)
        rcases hHprimes p hp (hpd.trans hdvd2) with rfl | rfl
        · exact h1.1 rfl
        · exact h1.2 rfl
      have htop : R₀.map f = ⊤ := Subgroup.index_eq_one.1 hone
      intro y hy
      have : (⟨y, hy⟩ : ↥H) ∈ R₀.map f := htop ▸ Subgroup.mem_top _
      obtain ⟨r, hr, hre⟩ := this
      exact ⟨r, ⟨r, hr, rfl⟩, congrArg Subtype.val hre⟩
  obtain ⟨s, hs, hsQ⟩ := h X R T hRsolv hRprimes hO hTR hT2 hSyl D π Q hQ hTQ hinv hRmap
  exact ⟨s, hs, fun i hi => (hsQ i hi).trans (Subgroup.map_mono inf_le_left)⟩

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8
