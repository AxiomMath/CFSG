module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixBar

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)

section Sup

variable {Y : Type*} [Group Y]

theorem exists_mul_of_mem_sup_of_commute {A C : Subgroup Y}
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) {x : Y} (hx : x ∈ A ⊔ C) :
    ∃ a ∈ A, ∃ c ∈ C, x = a * c := by
  let S : Subgroup Y :=
    { carrier := {x | ∃ a ∈ A, ∃ c ∈ C, x = a * c}
      one_mem' := ⟨1, A.one_mem, 1, C.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, c, hc, rfl⟩ ⟨a', ha', c', hc', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', c * c', C.mul_mem hc hc', ?_⟩
        calc a * c * (a' * c') = a * (c * a') * c' := by group
          _ = a * (a' * c) * c' := by rw [← hAC a' ha' c hc]
          _ = a * a' * (c * c') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, c, hc, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, c⁻¹, C.inv_mem hc, ?_⟩
        have h := hAC a ha c hc
        calc (a * c)⁻¹ = c⁻¹ * a⁻¹ := mul_inv_rev _ _
          _ = a⁻¹ * c⁻¹ := (Commute.inv_inv (show Commute a c from h)).eq.symm }
  have hle : A ⊔ C ≤ S := sup_le (fun a ha => ⟨a, ha, 1, C.one_mem, by simp⟩)
    (fun c hc => ⟨1, A.one_mem, c, hc, by simp⟩)
  exact hle hx

end Sup

section Component

variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}

omit [Finite Y] in
theorem mem_perfectJoin_subgroupOf {a : Y} (haL : a ∈ L) (hJL : J ≤ L)
    (ha : a ∈ perfectJoin J) : (⟨a, haL⟩ : ↥L) ∈ perfectJoin (J.subgroupOf L) := by
  have hVJ := perfectJoin_le J
  have hVp := perfectJoin_perfect J
  have hVL : perfectJoin J ≤ L := hVJ.trans hJL
  have hVsub : ⁅(perfectJoin J).subgroupOf L, (perfectJoin J).subgroupOf L⁆ =
      (perfectJoin J).subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hVL, hVp]
  have h1 := le_perfectJoin (J := J.subgroupOf L) (U := (perfectJoin J).subgroupOf L)
    (fun x hx => Subgroup.mem_subgroupOf.2 (hVJ (Subgroup.mem_subgroupOf.1 hx))) hVsub
  exact h1 (Subgroup.mem_subgroupOf.2 ha)

theorem exists_fixBarData_of_census {p : ℕ} {u : Y} (hparab : CompParab L J) (hp : p.Prime)
    (hcyc : CycPerfect p J) (hjoin : u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y))
    (hpow : u ^ p = 1) (hnot : u ∉ Subgroup.centralizer (L : Set Y))
    (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J) :
    ∃ (l : ↥L) (c : Y), c ∈ Subgroup.centralizer (L : Set Y) ∧ u = (l : Y) * c ∧
      l ^ p ∈ Subgroup.center ↥L ∧
      FixBarData ((J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) p
        (QuotientGroup.mk' (Subgroup.center ↥L) l) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJL : J ≤ L := hparab.parab.1
  obtain ⟨a, ha, c, hc, huac⟩ := exists_mul_of_mem_sup_of_commute
    (A := perfectJoin J) (C := Subgroup.centralizer (L : Set Y))
    (fun a ha c hc => (Subgroup.mem_centralizer_iff.1 hc) a
      ((perfectJoin_le J).trans hJL ha)) hjoin
  have haL : a ∈ L := hJL (perfectJoin_le J ha)
  set l : ↥L := ⟨a, haL⟩ with hl
  have hcomm : ∀ g : Y, g ∈ L → g * c = c * g := fun g hg =>
    (Subgroup.mem_centralizer_iff.1 hc) g hg
  have hlp : l ^ p ∈ Subgroup.center ↥L := by
    have hu := hpow
    rw [huac] at hu
    have hac : a * c = c * a := hcomm a haL
    have hpow : (a * c) ^ p = a ^ p * c ^ p := (Commute.mul_pow (hac : Commute a c) p)
    rw [hpow] at hu
    have hcp : c ^ p ∈ Subgroup.centralizer (L : Set Y) := Subgroup.pow_mem _ hc p
    have hap : a ^ p = (c ^ p)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact hu
    have hapc : a ^ p ∈ Subgroup.centralizer (L : Set Y) := by
      rw [hap]
      exact Subgroup.inv_mem _ hcp
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : Y) * a ^ p = a ^ p * (g : Y)
    exact (Subgroup.mem_centralizer_iff.1 hapc) (g : Y) g.2
  have hl1 : l ∉ (QuotientGroup.mk' (Subgroup.center ↥L)).ker := by
    rw [QuotientGroup.ker_mk']
    intro hz
    apply hnot
    have haC : a ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := Subgroup.mem_center_iff.1 hz ⟨g, hg⟩
      exact congrArg Subtype.val this
    rw [huac]
    exact Subgroup.mul_mem _ haC hc
  refine ⟨l, c, hc, huac, hlp, ?_⟩
  have hker : (QuotientGroup.mk' (Subgroup.center ↥L)).ker = Subgroup.center ↥L :=
    QuotientGroup.ker_mk' _
  refine fixBarData_of_central_quotient (G := ↥L) (J := J.subgroupOf L) (l := l)
    (ψ := QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
    hker.le (by rw [hker]; exact hparab.odd) hp ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    obtain ⟨-, T, ⟨hTL, hT2, hTi⟩, hNJ⟩ := hparab.parab
    refine ⟨T.subgroupOf L, ⟨le_top, hT2.comap_subtype (K := L), ?_⟩, ?_, ?_⟩
    · have e : ((T.subgroupOf L).subgroupOf ⊤).index = (T.subgroupOf L).index :=
        Subgroup.relIndex_top_right _
      rw [e]
      exact hTi
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      refine hNJ ⟨x.2, Subgroup.mem_normalizer_fintype fun t ht => ?_⟩
      have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ T.subgroupOf L := Subgroup.mem_subgroupOf.2 ht
      have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨t, hTL ht⟩).1 h1
      simpa [Subgroup.mem_subgroupOf] using h2
    · intro hJe
      apply hparab.ne_borel T ⟨hTL, hT2, hTi⟩
      refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
      · have hyL : y ∈ L := hJL hy
        refine ⟨hyL, ?_⟩
        have hyG : (⟨y, hyL⟩ : ↥L) ∈ J.subgroupOf L := Subgroup.mem_subgroupOf.2 hy
        rw [hJe] at hyG
        refine Subgroup.mem_normalizer_fintype fun t ht => ?_
        have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ T.subgroupOf L := Subgroup.mem_subgroupOf.2 ht
        have h2 := (Subgroup.mem_normalizer_iff.1 hyG ⟨t, hTL ht⟩).1 h1
        simpa [Subgroup.mem_subgroupOf] using h2
      · obtain ⟨hyL, hyN⟩ := hy
        have : (⟨y, hyL⟩ : ↥L) ∈ J.subgroupOf L := by
          rw [hJe, Subgroup.mem_normalizer_iff]
          intro g
          have := Subgroup.mem_normalizer_iff.1 hyN g.1
          simp only [Subgroup.mem_subgroupOf]
          exact this
        exact Subgroup.mem_subgroupOf.1 this
  · intro hJt
    apply hparab.ne_top
    refine le_antisymm hJL (fun y hy => ?_)
    have := (Subgroup.eq_top_iff' _).1 hJt ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.1 this
  · intro V hVJ hV Q hQV hQp
    have hV' : ⁅V.map L.subtype, V.map L.subtype⁆ = V.map L.subtype := by
      rw [← Subgroup.map_commutator, hV]
    have hVJ' : V.map L.subtype ≤ J := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hVJ hx)
    have : IsCyclic ↥(Q.map L.subtype) := hcyc (V.map L.subtype) hVJ' hV' (Q.map L.subtype)
      (Subgroup.map_mono hQV) (hQp.map L.subtype)
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective Q L.subtype L.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  · rw [hker]
    exact hlp
  · exact hl1
  · exact mem_perfectJoin_subgroupOf haL hJL ha
  · intro g hg
    rw [Subgroup.mem_subgroupOf]
    apply hfix g.1 g.2
    have h1 : (g : Y) * a = a * (g : Y) := congrArg Subtype.val hg
    have h2 : (g : Y) * c = c * (g : Y) := hcomm g g.2
    rw [huac]
    calc (a * c) * (g : Y) * (a * c)⁻¹ = a * (c * g) * (c⁻¹ * a⁻¹) := by group
      _ = a * (g * c) * (c⁻¹ * a⁻¹) := by rw [h2]
      _ = (a * g) * (c * c⁻¹) * a⁻¹ := by group
      _ = (g * a) * a⁻¹ := by rw [h1]; group
      _ = g := by group

theorem exists_fixBarData_of_fixPrimeHyp {p : ℕ} {u : Y} (h : FixPrimeHyp L J p u) :
    ∃ (l : ↥L) (c : Y), c ∈ Subgroup.centralizer (L : Set Y) ∧ u = (l : Y) * c ∧
      l ^ p ∈ Subgroup.center ↥L ∧
      FixBarData ((J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) p
        (QuotientGroup.mk' (Subgroup.center ↥L) l) :=
  exists_fixBarData_of_census h.parab h.prime h.cyc h.join h.pow h.not_mem h.fix

theorem exists_fixBarData_of_fixThreeHyp {u : Y} (h : FixThreeHyp L J u) :
    ∃ (l : ↥L) (c : Y), c ∈ Subgroup.centralizer (L : Set Y) ∧ u = (l : Y) * c ∧
      l ^ 3 ∈ Subgroup.center ↥L ∧
      FixBarData ((J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) 3
        (QuotientGroup.mk' (Subgroup.center ↥L) l) :=
  exists_fixBarData_of_census h.parab Nat.prime_three h.cyc h.join h.pow h.not_mem h.fix

theorem exists_fixBarData_full_of_census {p : ℕ} {u : Y} (hparab : CompParab L J) (hp : p.Prime)
    (hcyc : CycPerfect p J) (hjoin : u ∈ perfectJoin J ⊔ Subgroup.centralizer (L : Set Y))
    (hpow : u ^ p = 1) (hnot : u ∉ Subgroup.centralizer (L : Set Y))
    (hfix : ∀ l ∈ L, u * l * u⁻¹ = l → l ∈ J)
    (hZ : Nat.card (Subgroup.center ↥L) = 1) :
    ∃ v : ↥L ⧸ Subgroup.center ↥L,
      FixBarData ((J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) p v ∧
        ∀ g : ↥L ⧸ Subgroup.center ↥L, g * v = v * g →
          g ∈ (J.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
  obtain ⟨l, c, hc, huc, -, hbar⟩ := exists_fixBarData_of_census hparab hp hcyc hjoin hpow hnot hfix
  refine ⟨QuotientGroup.mk' (Subgroup.center ↥L) l, hbar, ?_⟩
  intro g hg
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) g
  have hker : (QuotientGroup.mk' (Subgroup.center ↥L)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', Subgroup.card_eq_one.1 hZ]
  have hcomm : g0 * l = l * g0 := by
    have h1 : (QuotientGroup.mk' (Subgroup.center ↥L)) (g0 * l) =
        (QuotientGroup.mk' (Subgroup.center ↥L)) (l * g0) := by
      rw [map_mul, map_mul]
      exact hg
    have := (MonoidHom.ker_eq_bot_iff _).1 hker h1
    exact this
  refine ⟨g0, ?_, rfl⟩
  change g0 ∈ J.subgroupOf L
  rw [Subgroup.mem_subgroupOf]
  apply hfix g0.1 g0.2
  have h1 : (g0 : Y) * (l : Y) = (l : Y) * (g0 : Y) := congrArg Subtype.val hcomm
  have h2 : (g0 : Y) * c = c * (g0 : Y) := (Subgroup.mem_centralizer_iff.1 hc) g0.1 g0.2
  rw [huc]
  generalize (l : Y) = a at h1 ⊢
  generalize (g0 : Y) = b at h1 h2 ⊢
  calc (a * c) * b * (a * c)⁻¹ = a * (c * b) * (c⁻¹ * a⁻¹) := by group
    _ = a * (b * c) * (c⁻¹ * a⁻¹) := by rw [← h2]
    _ = (a * b) * (c * c⁻¹) * a⁻¹ := by group
    _ = (b * a) * a⁻¹ := by rw [h1]; group
    _ = b := by group

end Component

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
