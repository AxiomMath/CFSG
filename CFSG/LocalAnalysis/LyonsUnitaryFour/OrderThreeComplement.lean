module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Local

public section

namespace CFSG.LyonsUnitaryFour

theorem oddCore_quotient_oddCore_eq_bot (X : Type*) [Group X] [Finite X] :
    CFSG.oddCore (X ⧸ CFSG.oddCore X) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := CFSG.oddCore X with hK
  set N := (CFSG.oddCore (X ⧸ K)).comap (QuotientGroup.mk' K) with hN
  have hNn : N.Normal := (CFSG.oddCore_normal _).comap _
  have hord : ∀ x ∈ N, Odd (orderOf x) := by
    intro x hx
    have hx' : QuotientGroup.mk' K x ∈ CFSG.oddCore (X ⧸ K) := hx
    have hm := CFSG.Adapters.odd_orderOf_of_mem_oddCore hx'
    set m := orderOf (QuotientGroup.mk' K x) with hmdef
    have hxm : x ^ m ∈ K := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, hmdef]
      exact pow_orderOf_eq_one _
    have ho := CFSG.Adapters.odd_orderOf_of_mem_oddCore hxm
    have hdvd : orderOf x ∣ m * orderOf (x ^ m) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact pow_orderOf_eq_one _
    exact (hm.mul ho).of_dvd_nat hdvd
  have hNodd : Odd (Nat.card N) := by
    by_contra heven
    rw [Nat.not_odd_iff_even] at heven
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 (even_iff_two_dvd.mp heven)
    have := hord y y.2
    rw [Subgroup.orderOf_coe, hy] at this
    exact (Nat.not_odd_iff_even.mpr even_two) this
  have hNK : N ≤ K := le_sSup ⟨hNn, hNodd⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hNK hy

theorem oddCore_characteristic (X : Type*) [Group X] [Finite X] :
    (CFSG.oddCore X).Characteristic := by
  rw [Subgroup.characteristic_iff_le_map]
  intro φ
  have hle : (CFSG.oddCore X).map φ.symm.toMonoidHom ≤ CFSG.oddCore X :=
    le_sSup ⟨(CFSG.oddCore_normal X).map _ φ.symm.surjective,
      by rw [Subgroup.card_map_of_injective φ.symm.injective]; exact odd_card_oddCore X⟩
  intro x hx
  refine ⟨φ.symm x, hle ⟨x, hx, rfl⟩, by simp⟩

theorem oddCore_map_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) : (CFSG.oddCore X).map e.toMonoidHom = CFSG.oddCore Y := by
  apply le_antisymm
  · exact le_sSup ⟨(CFSG.oddCore_normal X).map _ e.surjective,
      by rw [Subgroup.card_map_of_injective e.injective]; exact odd_card_oddCore X⟩
  · have hle : (CFSG.oddCore Y).map e.symm.toMonoidHom ≤ CFSG.oddCore X :=
      le_sSup ⟨(CFSG.oddCore_normal Y).map _ e.symm.surjective,
        by rw [Subgroup.card_map_of_injective e.symm.injective]; exact odd_card_oddCore Y⟩
    intro y hy
    exact ⟨e.symm y, hle ⟨y, hy, rfl⟩, by simp⟩

theorem le_normalizer_centralizer {G : Type*} [Group G] (S : Subgroup G) :
    S ≤ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro m
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hm x hx
    have h := hm (s⁻¹ * x * s)
      (by simpa [mul_assoc] using S.mul_mem (S.mul_mem (S.inv_mem hs) hx) hs)
    calc x * (s * m * s⁻¹) = s * ((s⁻¹ * x * s) * m) * s⁻¹ := by group
      _ = s * (m * (s⁻¹ * x * s)) * s⁻¹ := by rw [h]
      _ = s * m * s⁻¹ * x := by group
  · intro hm x hx
    have h := hm (s * x * s⁻¹) (S.mul_mem (S.mul_mem hs hx) (S.inv_mem hs))
    have h2 : s * x * m * s⁻¹ = s * m * x * s⁻¹ := by
      calc s * x * m * s⁻¹ = (s * x * s⁻¹) * (s * m * s⁻¹) := by group
        _ = (s * m * s⁻¹) * (s * x * s⁻¹) := h
        _ = s * m * x * s⁻¹ := by group
    have h3 := congrArg (fun g => s⁻¹ * g * s) h2
    simpa [mul_assoc] using h3

variable {G : Type} [Group G] [Finite G]

theorem lyons_order_three_centralizer_eq_sylow_mul_oddCore [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 3) {z : G}
    (hzZ : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype) (hz1 : z ≠ 1) :
    ∀ c : Subgroup.centralizer ({z} : Set G),
      ∃ s ∈ (S : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G)),
        ∃ k ∈ CFSG.oddCore (Subgroup.centralizer ({z} : Set G)), c = s * k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hZcomm, -, -, -, -, -, -, hidx3, -, -, hloc⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  set Sg := (S : Subgroup G) with hSg
  set Z := (Subgroup.center Sg).map Sg.subtype with hZ
  set N := Subgroup.normalizer (Sg : Set G) with hN
  set R := Sg ⊔ Subgroup.centralizer (Sg : Set G) with hR
  have hZS : ∀ w ∈ Z, w ∈ Sg := fun w hw => (mem_map_center_iff.mp hw).1
  have hRZ : R ≤ Subgroup.centralizer (Z : Set G) := by
    apply sup_le
    · intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact ((mem_map_center_iff.mp hw).2 s hs).symm
    · intro m hm
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact (Subgroup.mem_centralizer_iff.mp hm) w (hZS w hw)
  have hCNZ : ∀ n ∈ N, n ∈ Subgroup.centralizer (Z : Set G) → n ∈ R := by
    have hle : R.subgroupOf N ≤ (Subgroup.centralizer (Z : Set G)).subgroupOf N := by
      intro n hn
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hRZ hn
    have h1 := Subgroup.relIndex_mul_index hle
    rw [hd, hidx3] at h1
    have h2 : (R.subgroupOf N).relIndex ((Subgroup.centralizer (Z : Set G)).subgroupOf N) = 1 := by
      omega
    rw [Subgroup.relIndex_eq_one] at h2
    intro n hn hnZ
    have := h2 (show (⟨n, hn⟩ : N) ∈ (Subgroup.centralizer (Z : Set G)).subgroupOf N from hnZ)
    exact this
  have hRmul : ∀ n ∈ R, ∃ s ∈ Sg, ∃ m ∈ Subgroup.centralizer (Sg : Set G), n = s * m := by
    intro n hn
    have hn' : n ∈ ((Sg ⊔ Subgroup.centralizer (Sg : Set G) : Subgroup G) : Set G) := hn
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Sg _ (le_normalizer_centralizer Sg),
      Set.mem_mul] at hn'
    obtain ⟨s, hs, m, hm, rfl⟩ := hn'
    exact ⟨s, hs, m, hm, rfl⟩
  set C := Subgroup.centralizer ({z} : Set G) with hC
  set K := CFSG.oddCore C with hK
  have hSC : Sg ≤ C := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((mem_map_center_iff.mp hzZ).2 s hs)
  set SC : Subgroup C := Sg.subgroupOf C with hSCdef
  set ZC : Subgroup C := Z.subgroupOf C with hZCdef
  have hZCSC : ZC ≤ SC := by
    intro w hw
    rw [hZCdef, Subgroup.mem_subgroupOf] at hw
    rw [hSCdef, Subgroup.mem_subgroupOf]
    exact hZS _ hw
  set πK := QuotientGroup.mk' K with hπKdef
  have hπK : Function.Surjective πK := QuotientGroup.mk'_surjective K
  set E : Subgroup (C ⧸ K) := ZC.map πK with hEdef
  have hEc : E ≤ Subgroup.center (C ⧸ K) := (hloc z hzZ hz1).2.2
  have hEn : E.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_center_iff.mp (hEc ha) g, mul_inv_cancel_right]
    exact ha
  have hZCp : IsPGroup 2 ZC := by
    have hZp : IsPGroup 2 Z := (S.isPGroup'.to_le (fun w hw => hZS w hw))
    exact hZp.of_equiv (Subgroup.subgroupOfEquivOfLe (fun w hw => hSC (hZS w hw))).symm
  have hE2 : IsPGroup 2 E := hZCp.map πK
  set πE := QuotientGroup.mk' E with hπEdef
  have hπE : Function.Surjective πE := QuotientGroup.mk'_surjective E
  set π : C →* (C ⧸ K) ⧸ E := πE.comp πK with hπdef
  have hπ : Function.Surjective π := hπE.comp hπK
  have hcore : CFSG.oddCore ((C ⧸ K) ⧸ E) = ⊥ := by
    obtain ⟨hmap, -, -⟩ := oddCore_quotient_central_two E hEc hE2
    rw [← hmap, oddCore_quotient_oddCore_eq_bot, Subgroup.map_bot]
  have hπker : ∀ x y : C, π x = π y → ∃ w ∈ ZC, ∃ k ∈ K, y = x * w * k := by
    intro x y hxy
    have h1 : (πK x)⁻¹ * πK y ∈ E := by
      have := QuotientGroup.eq.mp (show (QuotientGroup.mk (πK x) : (C ⧸ K) ⧸ E) =
        QuotientGroup.mk (πK y) from hxy)
      exact this
    obtain ⟨w, hw, hwe⟩ := h1
    refine ⟨w, hw, (x * w)⁻¹ * y, ?_, by group⟩
    have h2 : πK (x * w) = πK y := by
      rw [map_mul, hwe, mul_inv_cancel_left]
    rw [hπKdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
    exact h2
  have hπZC : ∀ w ∈ ZC, π w = 1 := by
    intro w hw
    rw [hπdef, MonoidHom.comp_apply, hπEdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨w, hw, rfl⟩
  have hπK1 : ∀ k ∈ K, π k = 1 := by
    intro k hk
    show πE (πK k) = 1
    rw [show πK k = 1 from (QuotientGroup.eq_one_iff k).mpr hk, map_one]
  set SCs : Sylow 2 C := S.subtype hSC with hSCs
  have hSCs_coe : (SCs : Subgroup C) = SC := Sylow.coe_subtype _ _
  set Sbar : Sylow 2 ((C ⧸ K) ⧸ E) := SCs.mapSurjective hπ with hSbardef
  have hmemSbar : ∀ y, y ∈ (Sbar : Subgroup ((C ⧸ K) ⧸ E)) ↔ ∃ s ∈ SC, π s = y := by
    intro y
    rw [hSbardef, Sylow.coe_mapSurjective, Subgroup.mem_map, hSCs_coe]
  have hSbar_comm : ∀ s ∈ SC, ∀ s' ∈ SC, π s * π s' = π s' * π s := by
    intro s hs s' hs'
    have hcomm : s * s' * s⁻¹ * s'⁻¹ ∈ ZC := by
      rw [hZCdef, Subgroup.mem_subgroupOf, hZcomm]
      have := Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hs)
        (Subgroup.mem_subgroupOf.mp hs')
      simpa [commutatorElement_def] using this
    have h1 := hπZC _ hcomm
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π s * π s' = (π s * π s' * (π s)⁻¹ * (π s')⁻¹) * (π s' * π s) := by group
      _ = π s' * π s := by rw [h1, one_mul]
  have hle : Subgroup.normalizer ((Sbar : Subgroup ((C ⧸ K) ⧸ E)) : Set ((C ⧸ K) ⧸ E)) ≤
      Subgroup.centralizer ((Sbar : Subgroup ((C ⧸ K) ⧸ E)) : Set ((C ⧸ K) ⧸ E)) := by
    intro ybar hybar
    obtain ⟨c, rfl⟩ := hπ ybar
    have hA : ∀ s ∈ SC, c * s * c⁻¹ ∈ SC ⊔ K := by
      intro s hs
      have h1 : π (c * s * c⁻¹) ∈ (Sbar : Subgroup ((C ⧸ K) ⧸ E)) := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hybar (π s)).mp ((hmemSbar _).mpr ⟨s, hs, rfl⟩)
      obtain ⟨s', hs', hs'eq⟩ := (hmemSbar _).mp h1
      obtain ⟨w, hw, k, hk, hrepr⟩ := hπker s' (c * s * c⁻¹) hs'eq
      rw [hrepr]
      exact Subgroup.mul_mem_sup (SC.mul_mem hs' (hZCSC hw)) hk
    have hSCK : (SCs : Subgroup C) ≤ SC ⊔ K := hSCs_coe ▸ le_sup_left
    have hQ : SC.map (MulAut.conj c).toMonoidHom ≤ SC ⊔ K := by
      rintro _ ⟨s, hs, rfl⟩
      exact hA s hs
    have hQp : IsPGroup 2 (SC.map (MulAut.conj c).toMonoidHom) :=
      (hSCs_coe ▸ SCs.isPGroup').map _
    obtain ⟨v, hv, hvc⟩ := exists_conj_le_sylow_of_le SCs hSCK hQ hQp
    set n := v * c with hndef
    have hnN : ∀ s ∈ SC, n * s * n⁻¹ ∈ SC := by
      intro s hs
      have := hvc (c * s * c⁻¹) ⟨s, hs, rfl⟩
      rw [hSCs_coe] at this
      convert this using 1
      rw [hndef]; group
    have hnG : (n : G) ∈ N := by
      have hmap : Sg.map (MulAut.conj (n : G)).toMonoidHom = Sg := by
        apply Subgroup.eq_of_le_of_card_ge
        · rintro _ ⟨s, hs, rfl⟩
          have := hnN ⟨s, hSC hs⟩ (Subgroup.mem_subgroupOf.mpr hs)
          rw [Subgroup.mem_subgroupOf] at this
          simpa using this
        · rw [Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective]
      exact mem_normalizer_of_map_conj_eq hmap
    have hnZ : (n : G) ∈ Subgroup.centralizer (Z : Set G) := by
      have hmem : (n : G) ∈ N ⊓ Subgroup.centralizer ({z} : Set G) := ⟨hnG, n.2⟩
      rw [(hloc z hzZ hz1).1] at hmem
      exact hmem.2
    obtain ⟨s₀, hs₀, m, hm, hnsm⟩ := hRmul _ (hCNZ _ hnG hnZ)
    have hmC : m ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hm) z (hZS z hzZ)).symm
    set mC : C := ⟨m, hmC⟩ with hmCdef
    set s₀C : C := ⟨s₀, hSC hs₀⟩ with hs₀Cdef
    have hn_eq : n = s₀C * mC := Subtype.ext hnsm
    have hv' : v ∈ ((SC ⊔ K : Subgroup C) : Set C) := hv
    rw [Subgroup.mul_normal, Set.mem_mul] at hv'
    obtain ⟨s₁, hs₁, k₁, hk₁, hv_eq⟩ := hv'
    have hc_eq : c = v⁻¹ * n := by rw [hndef]; group
    have hπv : π v = π s₁ := by rw [← hv_eq, map_mul, hπK1 k₁ hk₁, mul_one]
    have hπc : π c = (π s₁)⁻¹ * (π s₀C * π mC) := by
      rw [hc_eq, map_mul, map_inv, hπv, hn_eq, map_mul]
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨s₂, hs₂, rfl⟩ := (hmemSbar b).mp hb
    have c1 : Commute (π s₂) (π s₁) := hSbar_comm s₂ hs₂ s₁ hs₁
    have c2 : Commute (π s₂) (π s₀C) :=
      hSbar_comm s₂ hs₂ s₀C (Subgroup.mem_subgroupOf.mpr hs₀)
    have c3 : Commute (π s₂) (π mC) := by
      show π s₂ * π mC = π mC * π s₂
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hm) s₂ (Subgroup.mem_subgroupOf.mp hs₂)
    rw [hπc]
    exact (c1.inv_right.mul_right (c2.mul_right c3)).eq
  have hcomp := MonoidHom.ker_transferSylow_isComplement' Sbar hle
  have hLodd : Odd (Nat.card (MonoidHom.transferSylow Sbar hle).ker) := by
    have hnd := Sbar.not_dvd_index
    rw [hcomp.index_eq_card] at hnd
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
  have hLbot : (MonoidHom.transferSylow Sbar hle).ker = ⊥ := by
    have hle' : (MonoidHom.transferSylow Sbar hle).ker ≤ CFSG.oddCore ((C ⧸ K) ⧸ E) :=
      le_sSup ⟨inferInstance, hLodd⟩
    rw [hcore] at hle'
    exact le_bot_iff.mp hle'
  have hStop : (Sbar : Subgroup ((C ⧸ K) ⧸ E)) = ⊤ := by
    have := hcomp.sup_eq_top
    rwa [hLbot, bot_sup_eq] at this
  intro c
  have hc : π c ∈ (Sbar : Subgroup ((C ⧸ K) ⧸ E)) := by rw [hStop]; exact Subgroup.mem_top _
  obtain ⟨s, hs, hsc⟩ := (hmemSbar (π c)).mp hc
  obtain ⟨w, hw, k, hk, hrepr⟩ := hπker s c hsc
  exact ⟨s * w, SC.mul_mem hs (hZCSC hw), k, hk, hrepr⟩

theorem lyons_order_three_normalizer_involution_complements [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 3) :
    (∀ z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, z ≠ 1 →
      (∀ c ∈ Subgroup.centralizer ({z} : Set G), ∃ s ∈ (S : Subgroup G),
        ∃ k ∈ (CFSG.oddCore (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype, c = s * k) ∧
      (S : Subgroup G) ⊓ (CFSG.oddCore (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype = ⊥ ∧
      Function.Bijective
        ((QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer ({z} : Set G)))).comp
          ((S : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G))).subtype)) ∧
    (∀ t : G, orderOf t = 2 →
      (CFSG.oddCore (Subgroup.centralizer ({t} : Set G))).Characteristic ∧
      ∃ P : Sylow 2 (Subgroup.centralizer ({t} : Set G)),
        CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) ⊔
            (P : Subgroup (Subgroup.centralizer ({t} : Set G))) = ⊤ ∧
        CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) ⊓
            (P : Subgroup (Subgroup.centralizer ({t} : Set G))) = ⊥) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hZcard, -, -, -, -, -, -, hconj, -⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  set Sg := (S : Subgroup G) with hSg
  set Z := (Subgroup.center Sg).map Sg.subtype with hZ
  have hone : ∀ z ∈ Z, z ≠ 1 →
      (∀ c ∈ Subgroup.centralizer ({z} : Set G), ∃ s ∈ Sg,
        ∃ k ∈ (CFSG.oddCore (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype, c = s * k) ∧
      Sg ⊓ (CFSG.oddCore (Subgroup.centralizer ({z} : Set G))).map
          (Subgroup.centralizer ({z} : Set G)).subtype = ⊥ ∧
      Function.Bijective
        ((QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer ({z} : Set G)))).comp
          (Sg.subgroupOf (Subgroup.centralizer ({z} : Set G))).subtype) := by
    intro z hzZ hz1
    set C := Subgroup.centralizer ({z} : Set G) with hC
    set K := CFSG.oddCore C with hK
    have hsplit := lyons_order_three_centralizer_eq_sylow_mul_oddCore hnonab hT S U hSU hd hzZ hz1
    have hinf : Sg ⊓ K.map C.subtype = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxS, ⟨k, hk, rfl⟩⟩
      rw [Subgroup.mem_bot]
      have hodd : Odd (orderOf (k : G)) := by
        rw [Subgroup.orderOf_coe]; exact CFSG.Adapters.odd_orderOf_of_mem_oddCore hk
      obtain ⟨j, hj⟩ := S.isPGroup' ⟨(k : G), hxS⟩
      have hdvd : orderOf (k : G) ∣ 2 ^ j := by
        apply orderOf_dvd_of_pow_eq_one
        have := congrArg Subtype.val hj
        simpa using this
      have hcop : Nat.Coprime (orderOf (k : G)) (2 ^ j) :=
        (Nat.coprime_two_right.mpr hodd).pow_right j
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
    refine ⟨?_, hinf, ?_, ?_⟩
    · intro c hc
      obtain ⟨s, hs, k, hk, h⟩ := hsplit ⟨c, hc⟩
      exact ⟨s, Subgroup.mem_subgroupOf.mp hs, k, ⟨k, hk, rfl⟩, congrArg Subtype.val h⟩
    · rw [injective_iff_map_eq_one]
      intro a ha
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
      have hmem : ((a : C) : G) ∈ Sg ⊓ K.map C.subtype :=
        ⟨Subgroup.mem_subgroupOf.mp a.2, ⟨a, ha, rfl⟩⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      exact Subtype.ext (Subtype.ext hmem)
    · intro y
      obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective K y
      obtain ⟨s, hs, k, hk, rfl⟩ := hsplit c
      refine ⟨⟨s, hs⟩, ?_⟩
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq]
      rw [inv_mul_cancel_left]
      exact hk
  refine ⟨hone, ?_⟩
  intro t ht
  refine ⟨oddCore_characteristic _, ?_⟩
  have hZcardG : Nat.card Z = 4 := by
    rw [hZ, Subgroup.card_map_of_injective Sg.subtype_injective, hZcard]
  obtain ⟨z₀, hz₀Z, hz₀1, -⟩ := exists_third_mem_four hZcardG (1 : G)
  have hz₀ord : orderOf z₀ = 2 := by
    obtain ⟨y, hy, rfl⟩ := hz₀Z
    rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
    obtain ⟨-, -, hsq1, -, -⟩ := unitary_four_sylow_structure hT S U hSU
    apply orderOf_eq_prime ((hsq1 y).mpr hy)
    intro h; apply hz₀1; rw [Subgroup.coe_subtype, h]; rfl
  obtain ⟨h, hh⟩ := isConj_iff.mp (hconj t z₀ ht hz₀ord)
  set Ct := Subgroup.centralizer ({t} : Set G) with hCt
  set Cz := Subgroup.centralizer ({z₀} : Set G) with hCz
  have hmap : Ct.map (MulAut.conj h).toMonoidHom = Cz := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hc' : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      show h * c * h⁻¹ * z₀ = z₀ * (h * c * h⁻¹)
      rw [← hh]
      calc h * c * h⁻¹ * (h * t * h⁻¹) = h * (c * t) * h⁻¹ := by group
        _ = h * (t * c) * h⁻¹ := by rw [hc']
        _ = h * t * h⁻¹ * (h * c * h⁻¹) := by group
    · intro hx
      refine ⟨h⁻¹ * x * h, Subgroup.mem_centralizer_singleton_iff.mpr ?_,
        by simp [MulAut.conj_apply, mul_assoc]⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      rw [← hh] at hx
      calc h⁻¹ * x * h * t = h⁻¹ * (x * (h * t * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * t * h⁻¹) * x) * h := by rw [hx]
        _ = t * (h⁻¹ * x * h) := by group
  let e : Ct ≃* Cz := ((MulAut.conj h).subgroupMap Ct).trans (MulEquiv.subgroupCongr hmap)
  obtain ⟨hz₀split, hz₀inf, -⟩ := hone z₀ hz₀Z hz₀1
  have hSCz : Sg ≤ Cz := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((mem_map_center_iff.mp hz₀Z).2 s hs)
  set Pz : Sylow 2 Cz := S.subtype hSCz with hPz
  have hPz_coe : (Pz : Subgroup Cz) = Sg.subgroupOf Cz := Sylow.coe_subtype _ _
  have hsupz : CFSG.oddCore Cz ⊔ (Pz : Subgroup Cz) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    obtain ⟨s, hs, k, ⟨k', hk', rfl⟩, hck⟩ := hz₀split c c.2
    have hc : c = ⟨s, hSCz hs⟩ * k' := Subtype.ext hck
    rw [hc, sup_comm]
    exact Subgroup.mul_mem_sup (by rw [hPz_coe]; exact Subgroup.mem_subgroupOf.mpr hs) hk'
  have hinfz : CFSG.oddCore Cz ⊓ (Pz : Subgroup Cz) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    obtain ⟨hcK, hcP⟩ := Subgroup.mem_inf.mp hc
    rw [hPz_coe, Subgroup.mem_subgroupOf] at hcP
    have hmem : (c : G) ∈ Sg ⊓ (CFSG.oddCore Cz).map Cz.subtype := ⟨hcP, ⟨c, hcK, rfl⟩⟩
    rw [hz₀inf, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).mpr (Subtype.ext hmem)
  set Pt : Sylow 2 Ct := Pz.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective with hPt
  have hPt_coe : (Pt : Subgroup Ct) = (Pz : Subgroup Cz).map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hKt : CFSG.oddCore Ct = (CFSG.oddCore Cz).map e.symm.toMonoidHom :=
    (oddCore_map_mulEquiv e.symm).symm
  refine ⟨Pt, ?_, ?_⟩
  · rw [hPt_coe, hKt, ← Subgroup.map_sup, hsupz]
    exact Subgroup.map_top_of_surjective _ e.symm.surjective
  · rw [hPt_coe, hKt, ← Subgroup.map_inf_eq _ _ _ e.symm.injective, hinfz, Subgroup.map_bot]

end CFSG.LyonsUnitaryFour
