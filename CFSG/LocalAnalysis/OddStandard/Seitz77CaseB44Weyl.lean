module

public import CFSG.LocalAnalysis.OddStandard.Seitz77LeviChart
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Fin
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Lift
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionDefs
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34

public section

namespace CFSG.OddStandard.Seitz77

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover CFSG.ComponentClassification
  CFSG.ComponentClassification.PSL3Four CFSG.OddStandard.Seitz77.L34
  CFSG.OddStandard.Seitz77.Levi CFSG.OddStandard.Seitz77.CaseB45 CFSG.ABGLocalTools
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.OddStandard.Seitz77.CaseBFin
open scoped commutatorElement

@[expose] def rootA : Subgroup ↥(unipAll F4) where
  carrier := {x | ∃ a : F4, x = ofCoords a 0 0}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨a', rfl⟩
    exact ⟨a + a', by rw [ofCoords_mul]; simp⟩
  one_mem' := ⟨0, ofCoords_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, by rw [ofCoords_inv]; simp⟩

@[expose] def rootB : Subgroup ↥(unipAll F4) where
  carrier := {x | ∃ b : F4, x = ofCoords 0 b 0}
  mul_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
    exact ⟨b + b', by rw [ofCoords_mul]; simp⟩
  one_mem' := ⟨0, ofCoords_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨b, rfl⟩
    exact ⟨-b, by rw [ofCoords_inv]; simp⟩

theorem exists_weyl_lifts {G : Type} [Group G] [Finite G]
    {A V : Subgroup G} (hZ : Odd (Nat.card (center ↥A)))
    (e : ↥A ⧸ center ↥A ≃* PSL3Four.S) (hV : IsSylowOf 2 V A) :
    ∃ (ι : ↥(unipAll F4) →* G) (σ₁ σ₂ : G), Function.Injective ι ∧ ι.range = V ∧
      σ₁ ∈ perfectResidualOf (A ⊓ normalizer ((U2.map ι : Subgroup G) : Set G)) ∧
      σ₂ ∈ perfectResidualOf (A ⊓ normalizer ((U1.map ι : Subgroup G) : Set G)) ∧
      cs σ₂ (rootA.map ι) = (U1 ⊓ U2).map ι ∧ cs σ₂ ((U1 ⊓ U2).map ι) = rootA.map ι ∧
      cs σ₁ (rootB.map ι) = (U1 ⊓ U2).map ι ∧ cs σ₁ ((U1 ⊓ U2).map ι) = rootB.map ι ∧
      (σ₁ * σ₂ * σ₁)⁻¹ * (σ₂ * σ₁ * σ₂) ∈ A ⊓ centralizer (A : Set G) ∧
      A ≤ (V ⊔ zpowers σ₁ ⊔ zpowers σ₂) ⊔ (A ⊓ centralizer (A : Set G)) := by
  classical
  let q : ↥A →* LinearFlag.projectiveSL 3 F4 :=
    theta.symm.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center ↥A)))
  have hq : Function.Surjective q :=
    theta.symm.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : q.ker = center ↥A := by
    ext x
    simp [q]
  have hP : Nat.card (LinearFlag.projectiveSL 3 F4) = 20160 := by
    rw [Nat.card_congr theta.toEquiv, card_S]
  obtain ⟨Q, hQ⟩ := hV
  obtain ⟨ι₀, h, g, hι₀, hr, -, -, -, hg⟩ :=
    exists_chart_of_hom_proj hq hker.le (by rw [hker]; exact hZ) hP Q
  have hodd : Odd (Nat.card q.ker) := by rw [hker]; exact hZ
  have hkodd : ∀ k : ↥A, q k = 1 → Odd (orderOf k) := fun k hk => by
    have hk' : k ∈ q.ker := hk
    have := orderOf_dvd_natCard (⟨k, hk'⟩ : q.ker)
    rw [Subgroup.orderOf_mk] at this
    exact hodd.of_dvd_nat this
  have hmemQ : ∀ u, ι₀ u ∈ (Q : Subgroup ↥A) := fun u => by
    rw [← hr]
    exact ⟨u, rfl⟩
  have h2elt : ∀ x ∈ (Q : Subgroup ↥A), ∃ m, orderOf x = 2 ^ m := fun x hx => by
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp Q.isPGroup' ⟨x, hx⟩
    exact ⟨m, by rwa [Subgroup.orderOf_mk] at hm⟩
  have lift_conj : ∀ (a : ↥A) (m : SpecialLinearGroup (Fin 3) F4),
      q a = q g * LinearFlag.proj 3 F4 m * (q g)⁻¹ → ∀ u u' : ↥(unipAll F4),
      m * (u : SpecialLinearGroup (Fin 3) F4) = (u' : SpecialLinearGroup (Fin 3) F4) * m →
      a * ι₀ u * a⁻¹ = ι₀ u' := by
    intro a m ha u u' hmu
    have hconj : LinearFlag.proj 3 F4 m * LinearFlag.proj 3 F4 (u : SpecialLinearGroup (Fin 3) F4) *
        (LinearFlag.proj 3 F4 m)⁻¹ =
        LinearFlag.proj 3 F4 (u' : SpecialLinearGroup (Fin 3) F4) := by
      rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, hmu]
    have hq1 : q (a * ι₀ u * a⁻¹) = q (ι₀ u') := by
      rw [hg u', ← hconj]
      simp only [map_mul, map_inv, hg u, ha]
      group
    refine eq_of_map_eq_of_two_power hker.le hkodd ?_ (h2elt _ (hmemQ u')) hq1
    obtain ⟨n, hn⟩ := h2elt _ (hmemQ u)
    exact ⟨n, by rw [← (SemiconjBy.conj_mk a (ι₀ u)).orderOf_eq]; exact hn⟩
  set ι : ↥(unipAll F4) →* G := A.subtype.comp ι₀ with hι
  have hιinj : Function.Injective ι := A.subtype_injective.comp hι₀
  have hιV : ι.range = V := by
    rw [hι, MonoidHom.range_comp, hr, ← hQ]
  have hιapp : ∀ u, ι u = ((ι₀ u : ↥A) : G) := fun u => rfl
  have construct : ∀ (lev : SpecialLinearGroup (Fin 2) F4 →* SpecialLinearGroup (Fin 3) F4)
      (s : SpecialLinearGroup (Fin 3) F4) (Ω : Subgroup G),
      ⁅lev.range, lev.range⁆ = lev.range → s ∈ lev.range →
      (∀ a : ↥A, (∃ B, q a = q g * LinearFlag.proj 3 F4 (lev B) * (q g)⁻¹) → (a : G) ∈ Ω) →
      ∃ a : ↥A, q a = q g * LinearFlag.proj 3 F4 s * (q g)⁻¹ ∧
        (a : G) ∈ perfectResidualOf Ω := by
    intro lev s Ω hperf hs hΩ
    let Λ : Subgroup (LinearFlag.projectiveSL 3 F4) :=
      ((lev.range).map (LinearFlag.proj 3 F4)).map (MulAut.conj (q g)).toMonoidHom
    have hΛ : ⁅Λ, Λ⁆ = Λ := by
      show ⁅_, _⁆ = _
      rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hperf]
    have hmemΛ : ∀ x, x ∈ Λ ↔ ∃ B, x = q g * LinearFlag.proj 3 F4 (lev B) * (q g)⁻¹ := by
      intro x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
        obtain ⟨B, rfl⟩ := hz
        exact ⟨B, rfl⟩
      · rintro ⟨B, rfl⟩
        exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_map.mpr ⟨lev B, ⟨B, rfl⟩, rfl⟩, rfl⟩
    refine exists_mem_perfectResidualOf_lift q hq hΛ (fun a ha => hΩ a ?_)
      ((hmemΛ _).mpr (by obtain ⟨B, rfl⟩ := hs; exact ⟨B, rfl⟩))
    obtain ⟨B, hB⟩ := (hmemΛ _).mp ha
    exact ⟨B, hB⟩
  have hΩ1 : ∀ a : ↥A, (∃ B, q a = q g * LinearFlag.proj 3 F4 (leviOne F4 B) * (q g)⁻¹) →
      (a : G) ∈ A ⊓ normalizer ((U1.map ι : Subgroup G) : Set G) := by
    rintro a ⟨B, hB⟩
    refine ⟨a.2, Subgroup.mem_normalizer_fintype fun n hn => ?_⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hn
    obtain ⟨a', b', c', rfl⟩ := exists_ofCoords u
    have hb : b' = 0 := ofCoords_mem_U1.mp hu
    subst hb
    obtain ⟨a'', c'', hmul⟩ := leviOne_mul_unipU_exists B a' c'
    have key := lift_conj a (leviOne F4 B) hB (ofCoords a' 0 c') (ofCoords a'' 0 c'') hmul
    refine Subgroup.mem_map.mpr ⟨ofCoords a'' 0 c'', ofCoords_mem_U1.mpr rfl, ?_⟩
    have := congrArg A.subtype key
    simpa [hιapp] using this.symm
  have hΩ2 : ∀ a : ↥A, (∃ B, q a = q g * LinearFlag.proj 3 F4 (leviTwo F4 B) * (q g)⁻¹) →
      (a : G) ∈ A ⊓ normalizer ((U2.map ι : Subgroup G) : Set G) := by
    rintro a ⟨B, hB⟩
    refine ⟨a.2, Subgroup.mem_normalizer_fintype fun n hn => ?_⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hn
    obtain ⟨a', b', c', rfl⟩ := exists_ofCoords u
    have ha : a' = 0 := ofCoords_mem_U2.mp hu
    subst ha
    obtain ⟨b'', c'', hmul⟩ := leviTwo_mul_unipU_exists B b' c'
    have key := lift_conj a (leviTwo F4 B) hB (ofCoords 0 b' c') (ofCoords 0 b'' c'') hmul
    refine Subgroup.mem_map.mpr ⟨ofCoords 0 b'' c'', ofCoords_mem_U2.mpr rfl, ?_⟩
    have := congrArg A.subtype key
    simpa [hιapp] using this.symm
  obtain ⟨a₂, ha₂q, ha₂P⟩ := construct (leviOne F4) weylS2 _ perfect_range_leviOne
    weylS2_mem_range hΩ1
  obtain ⟨a₁, ha₁q, ha₁P⟩ := construct (leviTwo F4) weylS1 _ perfect_range_leviTwo
    weylS1_mem_range hΩ2
  have hσ₂ : ∀ a c : F4, (a₂ : G) * ι (ofCoords a 0 c) * (a₂ : G)⁻¹ = ι (ofCoords c 0 a) := by
    intro a c
    have key := lift_conj a₂ weylS2 ha₂q (ofCoords a 0 c) (ofCoords c 0 a) (weylS2_mul_unipU a c)
    have := congrArg A.subtype key
    simpa [hιapp] using this
  have hσ₁ : ∀ b c : F4, (a₁ : G) * ι (ofCoords 0 b c) * (a₁ : G)⁻¹ = ι (ofCoords 0 c b) := by
    intro b c
    have key := lift_conj a₁ weylS1 ha₁q (ofCoords 0 b c) (ofCoords 0 c b) (weylS1_mul_unipU b c)
    have := congrArg A.subtype key
    simpa [hιapp] using this
  have hbraid : (a₁ * a₂ * a₁)⁻¹ * (a₂ * a₁ * a₂) ∈ center ↥A := by
    rw [← hker, MonoidHom.mem_ker]
    have key : ∀ (c p₁ p₂ : LinearFlag.projectiveSL 3 F4), p₁ * p₂ * p₁ = p₂ * p₁ * p₂ →
        ((c * p₁ * c⁻¹) * (c * p₂ * c⁻¹) * (c * p₁ * c⁻¹))⁻¹ *
          ((c * p₂ * c⁻¹) * (c * p₁ * c⁻¹) * (c * p₂ * c⁻¹)) = 1 := by
      intro c p₁ p₂ hb
      have : ((c * p₁ * c⁻¹) * (c * p₂ * c⁻¹) * (c * p₁ * c⁻¹))⁻¹ *
          ((c * p₂ * c⁻¹) * (c * p₁ * c⁻¹) * (c * p₂ * c⁻¹)) =
          c * ((p₁ * p₂ * p₁)⁻¹ * (p₂ * p₁ * p₂)) * c⁻¹ := by group
      rw [this, hb]
      group
    have hb := congrArg (LinearFlag.proj 3 F4) weyl_braid
    simp only [map_mul] at hb
    simp only [map_mul, map_inv, ha₁q, ha₂q]
    exact key _ _ _ hb
  set H₀ : Subgroup ↥A := ι₀.range ⊔ zpowers a₁ ⊔ zpowers a₂ with hH₀
  have hqtop : Subgroup.map q H₀ = ⊤ := by
    set φ : SpecialLinearGroup (Fin 3) F4 →* LinearFlag.projectiveSL 3 F4 :=
      (MulAut.conj (q g)).toMonoidHom.comp (LinearFlag.proj 3 F4) with hφ
    have hφapp : ∀ s, φ s = q g * LinearFlag.proj 3 F4 s * (q g)⁻¹ := fun s => rfl
    have hK : (Subgroup.map q H₀).comap φ = ⊤ := by
      rw [eq_top_iff, ← unipAll_sup_weyl_eq_top, sup_le_iff, sup_le_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro u hu
        show φ u ∈ Subgroup.map q H₀
        refine ⟨ι₀ ⟨u, hu⟩, mem_sup_left (mem_sup_left ⟨_, rfl⟩), ?_⟩
        rw [hg ⟨u, hu⟩, hφapp]
      · rw [Subgroup.zpowers_le]
        show φ weylS1 ∈ Subgroup.map q H₀
        exact ⟨a₁, mem_sup_left (mem_sup_right (mem_zpowers _)), by rw [ha₁q, hφapp]⟩
      · rw [Subgroup.zpowers_le]
        show φ weylS2 ∈ Subgroup.map q H₀
        exact ⟨a₂, mem_sup_right (mem_zpowers _), by rw [ha₂q, hφapp]⟩
    have hφs : Function.Surjective φ :=
      (MulAut.conj (q g)).surjective.comp (LinearFlag.proj_surjective 3 F4)
    rw [eq_top_iff]
    intro x _
    obtain ⟨s, rfl⟩ := hφs x
    have : s ∈ (Subgroup.map q H₀).comap φ := by rw [hK]; trivial
    exact this
  have hcs : ∀ (σ : G) (R R' : Subgroup ↥(unipAll F4)),
      (∀ x ∈ R, σ * ι x * σ⁻¹ ∈ R'.map ι) → (∀ y ∈ R', σ⁻¹ * ι y * σ ∈ R.map ι) →
      cs σ (R.map ι) = R'.map ι := by
    intro σ R R' h1 h2
    ext y
    rw [mem_cs]
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      have : y = σ * ι x * σ⁻¹ := by rw [hxy]; group
      rw [this]
      exact h1 x hx
    · intro hy
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      exact h2 y' hy'
  have hinv : ∀ (σ x y : G), σ * x * σ⁻¹ = y → σ⁻¹ * y * σ = x := by
    intro σ x y h
    rw [← h]
    group
  have hUc : ∀ x : ↥(unipAll F4), x ∈ U1 ⊓ U2 ↔ ∃ c, x = ofCoords 0 0 c := by
    intro x
    obtain ⟨a, b, c, rfl⟩ := exists_ofCoords x
    rw [Subgroup.mem_inf, ofCoords_mem_U1, ofCoords_mem_U2]
    constructor
    · rintro ⟨hb, ha⟩
      exact ⟨c, by rw [ha, hb]⟩
    · rintro ⟨c', h⟩
      rw [ofCoords_inj] at h
      exact ⟨h.2.1, h.1⟩
  have hcent : ∀ z : ↥A, z ∈ center ↥A → (z : G) ∈ A ⊓ centralizer (A : Set G) := by
    intro z hz
    rw [← map_center_subtype_eq_inf_centralizer]
    exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  refine ⟨ι, (a₁ : G), (a₂ : G), hιinj, hιV, ha₁P, ha₂P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine hcs _ _ _ ?_ ?_
    · rintro x ⟨a, rfl⟩
      exact Subgroup.mem_map.mpr ⟨ofCoords 0 0 a, (hUc _).mpr ⟨a, rfl⟩, (hσ₂ a 0).symm⟩
    · intro y hy
      obtain ⟨c, rfl⟩ := (hUc y).mp hy
      exact Subgroup.mem_map.mpr ⟨ofCoords c 0 0, ⟨c, rfl⟩,
        (hinv _ _ _ (hσ₂ c 0)).symm⟩
  · refine hcs _ _ _ ?_ ?_
    · intro x hx
      obtain ⟨c, rfl⟩ := (hUc x).mp hx
      exact Subgroup.mem_map.mpr ⟨ofCoords c 0 0, ⟨c, rfl⟩, (hσ₂ 0 c).symm⟩
    · rintro y ⟨a, rfl⟩
      exact Subgroup.mem_map.mpr ⟨ofCoords 0 0 a, (hUc _).mpr ⟨a, rfl⟩,
        (hinv _ _ _ (hσ₂ 0 a)).symm⟩
  · refine hcs _ _ _ ?_ ?_
    · rintro x ⟨b, rfl⟩
      exact Subgroup.mem_map.mpr ⟨ofCoords 0 0 b, (hUc _).mpr ⟨b, rfl⟩, (hσ₁ b 0).symm⟩
    · intro y hy
      obtain ⟨c, rfl⟩ := (hUc y).mp hy
      exact Subgroup.mem_map.mpr ⟨ofCoords 0 c 0, ⟨c, rfl⟩,
        (hinv _ _ _ (hσ₁ c 0)).symm⟩
  · refine hcs _ _ _ ?_ ?_
    · intro x hx
      obtain ⟨c, rfl⟩ := (hUc x).mp hx
      exact Subgroup.mem_map.mpr ⟨ofCoords 0 c 0, ⟨c, rfl⟩, (hσ₁ 0 c).symm⟩
    · rintro y ⟨b, rfl⟩
      exact Subgroup.mem_map.mpr ⟨ofCoords 0 0 b, (hUc _).mpr ⟨b, rfl⟩,
        (hinv _ _ _ (hσ₁ 0 b)).symm⟩
  · simpa using hcent _ hbraid
  · intro x hx
    obtain ⟨y, hy, hyq⟩ : ∃ y ∈ H₀, q y = q ⟨x, hx⟩ := by
      have : q ⟨x, hx⟩ ∈ Subgroup.map q H₀ := by rw [hqtop]; trivial
      obtain ⟨y, hy, hyq⟩ := this
      exact ⟨y, hy, hyq⟩
    have hz : y⁻¹ * ⟨x, hx⟩ ∈ center ↥A := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyq, inv_mul_cancel]
    have hH₀le : H₀.map A.subtype ≤ V ⊔ zpowers (a₁ : G) ⊔ zpowers (a₂ : G) := by
      rw [hH₀, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      refine sup_le_sup (sup_le_sup ?_ le_rfl) le_rfl
      rw [← hιV, hι, MonoidHom.range_comp]
    have hxe : x = ((y : ↥A) : G) * (((y⁻¹ * ⟨x, hx⟩ : ↥A)) : G) := by simp
    rw [hxe]
    exact Subgroup.mul_mem_sup (hH₀le (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)) (hcent _ hz)

theorem rootA_le_U1 : rootA ≤ U1 := by
  rintro _ ⟨a, rfl⟩
  exact ofCoords_mem_U1.mpr rfl

theorem rootB_le_U2 : rootB ≤ U2 := by
  rintro _ ⟨b, rfl⟩
  exact ofCoords_mem_U2.mpr rfl

theorem rootA_inf_eq_bot : rootA ⊓ (U1 ⊓ U2) = ⊥ := by
  refine eq_bot_iff.mpr ?_
  rintro x ⟨⟨a, rfl⟩, hx⟩
  have hx' : ofCoords a 0 0 ∈ U1 ⊓ U2 := hx
  rw [Subgroup.mem_inf, ofCoords_mem_U1, ofCoords_mem_U2] at hx'
  have ha : a = 0 := hx'.2
  subst ha
  exact ofCoords_zero

theorem rootB_inf_eq_bot : rootB ⊓ (U1 ⊓ U2) = ⊥ := by
  refine eq_bot_iff.mpr ?_
  rintro x ⟨⟨b, rfl⟩, hx⟩
  have hx' : ofCoords 0 b 0 ∈ U1 ⊓ U2 := hx
  rw [Subgroup.mem_inf, ofCoords_mem_U1, ofCoords_mem_U2] at hx'
  have hb : b = 0 := hx'.1
  subst hb
  exact ofCoords_zero

structure WeylInput {G : Type} [Group G] [Finite G] (A V V₁ V₂ : Subgroup G) (σa σb : G)
    (Up Uq : Subgroup G) : Prop where
  σa_mem : σa ∈ perfectResidualOf (A ⊓ normalizer (V₁ : Set G))
  σb_mem : σb ∈ perfectResidualOf (A ⊓ normalizer (V₂ : Set G))
  Up_le : Up ≤ V₁
  Uq_le : Uq ≤ V₂
  Up_inf : Up ⊓ (V₁ ⊓ V₂) = ⊥
  Uq_inf : Uq ⊓ (V₁ ⊓ V₂) = ⊥
  cs_a1 : cs σa Up = V₁ ⊓ V₂
  cs_a2 : cs σa (V₁ ⊓ V₂) = Up
  cs_b1 : cs σb Uq = V₁ ⊓ V₂
  cs_b2 : cs σb (V₁ ⊓ V₂) = Uq
  braid : (σb * σa * σb)⁻¹ * (σa * σb * σa) ∈ A ⊓ centralizer (A : Set G)
  gen : A ≤ (V ⊔ zpowers σa ⊔ zpowers σb) ⊔ (A ⊓ centralizer (A : Set G))

theorem exists_weylInput {G : Type} [Group G] [Finite G]
    {A V₁ V₂ : Subgroup G} (h : Hyp G A) (d : Datum A) (hR : Radicals d.V V₁ V₂) :
    ∃ (σa σb : G) (Up Uq : Subgroup G), WeylInput A d.V V₁ V₂ σa σb Up Uq := by
  obtain ⟨e⟩ := h.nonempty_equiv_S
  obtain ⟨ι, σ₁, σ₂, hι, hιV, hσ₁P, hσ₂P, c21, c22, c11, c12, hbr, hgen⟩ :=
    exists_weyl_lifts h.odd e d.V_isSylow
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, -⟩ := radicals_of_chart hι hιV
  have hZ : (U1 ⊓ U2).map ι = U1.map ι ⊓ U2.map ι := Subgroup.map_inf _ _ ι hι
  have hV₁ := h13 V₁ hR.le₁ hR.elem₁ hR.card₁
  have hV₂ := h13 V₂ hR.le₂ hR.elem₂ hR.card₂
  have hne : V₁ ≠ V₂ := by
    intro heq
    have h4 := hR.card_center
    rw [← hR.inf_eq, heq, inf_idem, ← heq, hR.card₁] at h4
    omega
  have hUp : ∀ (R : Subgroup ↥(unipAll F4)), R ⊓ (U1 ⊓ U2) = ⊥ →
      R.map ι ⊓ (U1.map ι ⊓ U2.map ι) = ⊥ := by
    intro R hRb
    rw [← hZ, ← Subgroup.map_inf _ _ ι hι, hRb, Subgroup.map_bot]
  rcases hV₁ with h1 | h1 <;> rcases hV₂ with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · subst h1 h2
    refine ⟨σ₂, σ₁, rootA.map ι, rootB.map ι, ⟨hσ₂P, hσ₁P, Subgroup.map_mono rootA_le_U1,
      Subgroup.map_mono rootB_le_U2, hUp _ rootA_inf_eq_bot, hUp _ rootB_inf_eq_bot,
      by rw [← hZ]; exact c21, by rw [← hZ]; exact c22, by rw [← hZ]; exact c11,
      by rw [← hZ]; exact c12, hbr, ?_⟩⟩
    have hc : d.V ⊔ zpowers σ₂ ⊔ zpowers σ₁ = d.V ⊔ zpowers σ₁ ⊔ zpowers σ₂ :=
      sup_right_comm _ _ _
    rw [hc]
    exact hgen
  · subst h1 h2
    refine ⟨σ₁, σ₂, rootB.map ι, rootA.map ι, ⟨hσ₁P, hσ₂P, Subgroup.map_mono rootB_le_U2,
      Subgroup.map_mono rootA_le_U1,
      by rw [inf_comm (Subgroup.map ι U2)]; exact hUp _ rootB_inf_eq_bot,
      by rw [inf_comm (Subgroup.map ι U2)]; exact hUp _ rootA_inf_eq_bot,
      by rw [inf_comm, ← hZ]; exact c11, by rw [inf_comm, ← hZ]; exact c12,
      by rw [inf_comm, ← hZ]; exact c21, by rw [inf_comm, ← hZ]; exact c22, ?_, ?_⟩⟩
    · have := Subgroup.inv_mem _ hbr
      simpa using this
    · exact hgen
  · exact absurd (h1.trans h2.symm) hne

end CFSG.OddStandard.Seitz77
