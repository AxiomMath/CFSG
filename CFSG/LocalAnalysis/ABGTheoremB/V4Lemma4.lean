module

public import CFSG.LocalAnalysis.ABGTheoremB.V4Lemma3
public import CFSG.LocalAnalysis.ABGTheoremB.V4Lemma4Core

public section

namespace CFSG.ABGTheoremB.V4

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGTheoremB.TotallyInverted
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem subgroupOf_le_normalizer' {B A C : Subgroup G}
    (h : A ≤ Subgroup.normalizer (C : Set G)) :
    A.subgroupOf B ≤ Subgroup.normalizer ((C.subgroupOf B : Subgroup B) : Set B) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (h ha) b

section Quotient

variable {B M : Subgroup G} [(M.subgroupOf B).Normal]

theorem mk'_eq_one_iff {g : G} (hg : g ∈ B) :
    QuotientGroup.mk' (M.subgroupOf B) ⟨g, hg⟩ = 1 ↔ g ∈ M := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem mk'_eq_mk'_iff {g h : G} (hg : g ∈ B) (hh : h ∈ B) :
    QuotientGroup.mk' (M.subgroupOf B) ⟨g, hg⟩ = QuotientGroup.mk' (M.subgroupOf B) ⟨h, hh⟩ ↔
      g⁻¹ * h ∈ M := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem mem_map_subgroupOf_iff {A : Subgroup G} (hAB : A ≤ B) {γ : ↥B ⧸ M.subgroupOf B} :
    γ ∈ (A.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B)) ↔
      ∃ a, ∃ ha : a ∈ A, QuotientGroup.mk' (M.subgroupOf B) ⟨a, hAB ha⟩ = γ := by
  constructor
  · rintro ⟨⟨a, haB⟩, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hAB ha⟩, ha, rfl⟩

theorem mk'_mem_map_subgroupOf {A : Subgroup G} {a : G} (ha : a ∈ A) (haB : a ∈ B) :
    QuotientGroup.mk' (M.subgroupOf B) ⟨a, haB⟩ ∈
      (A.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B)) :=
  ⟨⟨a, haB⟩, ha, rfl⟩

theorem card_map_subgroupOf_dvd {A : Subgroup G} (hAB : A ≤ B) :
    Nat.card ((A.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B))) ∣ Nat.card A := by
  have h := Subgroup.card_map_dvd (A.subgroupOf B) (QuotientGroup.mk' (M.subgroupOf B))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv] at h

theorem card_map_subgroupOf_of_inf_eq_bot {A : Subgroup G} (hAB : A ≤ B) (hAM : A ⊓ M = ⊥) :
    Nat.card ((A.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B))) = Nat.card A := by
  set f := (QuotientGroup.mk' (M.subgroupOf B)).comp (A.subgroupOf B).subtype with hf
  have hinj : Function.Injective f := by
    intro a b hab
    have h : QuotientGroup.mk' (M.subgroupOf B) (a : B) =
        QuotientGroup.mk' (M.subgroupOf B) (b : B) := hab
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    have hA : ((((a : B)⁻¹ * b : B)) : G) ∈ A :=
      (A.subgroupOf B).mul_mem ((A.subgroupOf B).inv_mem a.2) b.2
    have hmem : ((((a : B)⁻¹ * b : B)) : G) ∈ A ⊓ M := ⟨hA, h⟩
    rw [hAM, Subgroup.mem_bot] at hmem
    have : ((a : B)⁻¹ * b : B) = 1 := Subtype.ext hmem
    exact Subtype.ext (inv_mul_eq_one.mp this)
  have hrange : (A.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B)) =
      (⊤ : Subgroup (A.subgroupOf B)).map f := by
    rw [← MonoidHom.range_eq_map, hf, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv]

theorem map_subgroupOf_mul_comm {X Y : Subgroup G} (hX : X ≤ B) (hY : Y ≤ B)
    (hXY : (X : Set G) * Y = Y * X) :
    (((X.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B)) : Subgroup _) :
        Set (↥B ⧸ M.subgroupOf B)) *
      (((Y.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B)) : Subgroup _) :
        Set (↥B ⧸ M.subgroupOf B)) =
    (((Y.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B)) : Subgroup _) :
        Set (↥B ⧸ M.subgroupOf B)) *
      (((X.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B)) : Subgroup _) :
        Set (↥B ⧸ M.subgroupOf B)) := by
  have key : ∀ (X Y : Subgroup G) (hX : X ≤ B) (hY : Y ≤ B), (X : Set G) * Y = Y * X →
      (((X.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B)) : Subgroup _) :
          Set (↥B ⧸ M.subgroupOf B)) *
        (((Y.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B)) : Subgroup _) :
          Set (↥B ⧸ M.subgroupOf B)) ⊆
      (((Y.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B)) : Subgroup _) :
          Set (↥B ⧸ M.subgroupOf B)) *
        (((X.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B)) : Subgroup _) :
          Set (↥B ⧸ M.subgroupOf B)) := by
    intro X Y hX hY hXY
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    have hab : (a : G) * b ∈ (X : Set G) * Y := ⟨a, ha, b, hb, rfl⟩
    rw [hXY] at hab
    obtain ⟨b', hb', a', ha', he⟩ := hab
    refine ⟨QuotientGroup.mk' (M.subgroupOf B) ⟨b', hY hb'⟩, ⟨⟨b', hY hb'⟩, hb', rfl⟩,
      QuotientGroup.mk' (M.subgroupOf B) ⟨a', hX ha'⟩, ⟨⟨a', hX ha'⟩, ha', rfl⟩, ?_⟩
    show QuotientGroup.mk' (M.subgroupOf B) ⟨b', hY hb'⟩ *
      QuotientGroup.mk' (M.subgroupOf B) ⟨a', hX ha'⟩ =
      QuotientGroup.mk' (M.subgroupOf B) a * QuotientGroup.mk' (M.subgroupOf B) b
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext he
  exact Set.Subset.antisymm (key X Y hX hY hXY) (key Y X hY hX hXY.symm)

theorem map_subgroupOf_le_normalizer {A C : Subgroup G}
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) :
    (A.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B)) ≤
      Subgroup.normalizer ((C.subgroupOf B).map (QuotientGroup.mk' (M.subgroupOf B)) :
        Set (↥B ⧸ M.subgroupOf B)) :=
  (Subgroup.map_mono (subgroupOf_le_normalizer' hAC)).trans (Subgroup.le_normalizer_map _)

end Quotient

variable {σ : Setting G} {J W : Subgroup G}

theorem card_sup_dvd_of_mul_comm {R Y : Subgroup G} (hRY : (R : Set G) * Y = Y * R) :
    Nat.card (R ⊔ Y : Subgroup G) ∣ Nat.card R * Nat.card Y := by
  have h1 := Subgroup.relIndex_mul_card Y (R ⊔ Y)
  rw [inf_eq_left.mpr (le_sup_right : Y ≤ R ⊔ Y), Omnibus.relIndex_sup_of_mul_comm hRY] at h1
  rw [← h1]
  exact Nat.mul_dvd_mul_right (Subgroup.relIndex_dvd_card Y R) _

variable [Finite G] in
theorem lemmaV44 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJ : σ.IsV21Layer J)
    (h31 : LemmaV31Input σ J) (hN' : CommutatorInput σ) (h42 : LemmaII42Input σ J)
    (h46 : LemmaII46Input σ J) (h21 : ∀ r : ℕ, σ.HypIV7 r → r = σ.p)
    (hQF : Sec10.QGroupFourFusion G) (hW : W ∈ σ.familyW J) {R Y : Subgroup G}
    (hRp : IsPGroup σ.p R) (hDR : σ.D ≤ Subgroup.normalizer (R : Set G)) {r : ℕ} (hr : r.Prime)
    (hrW : r ∣ Nat.card W) (hYr : IsPGroup r Y) (hDY : σ.D ≤ Subgroup.normalizer (Y : Set G))
    (hRY : (R : Set G) * Y = Y * R) (hYW : Odd (Nat.card (Y ⊔ W : Subgroup G))) :
    ⁅R, σ.T⁆ ≤ pCoreIn σ.p (R ⊔ Y) := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  have : Fact r.Prime := ⟨hr⟩
  have hrp : r ≠ σ.p := fun h => h31.coprime W hW (h ▸ hrW)
  have hpr : σ.p ≠ r := fun h => hrp h.symm
  set K : Subgroup G := R ⊔ Y with hKdef
  set Op : Subgroup G := pCoreIn σ.p K with hOpdef
  have hTD := σ.T_le_D hσ
  have hTR : σ.T ≤ Subgroup.normalizer (R : Set G) := hTD.trans hDR
  have hTY : σ.T ≤ Subgroup.normalizer (Y : Set G) := hTD.trans hDY
  have hRodd : Odd (Nat.card R) := Omnibus.odd_card_of_isPGroup hσ.p_prime hσ.p_ne_two hRp
  have hYodd : Odd (Nat.card Y) := odd_card_of_le le_sup_left hYW
  have hKdvd : Nat.card K ∣ Nat.card R * Nat.card Y := card_sup_dvd_of_mul_comm hRY
  have hKodd : Odd (Nat.card K) := (hRodd.mul hYodd).of_dvd_nat hKdvd
  have hTK : σ.T ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf hTR hTY).trans (normalizer_inf_normalizer_le_normalizer_sup R Y)
  have hKOp : K ≤ Subgroup.normalizer (Op : Set G) := DataConstruction.le_normalizer_pCoreIn _ _
  have hTOp : σ.T ≤ Subgroup.normalizer (Op : Set G) :=
    hTK.trans (DataConstruction.normalizer_le_normalizer_pCoreIn _ _)
  have hOpp : IsPGroup σ.p Op := DataConstruction.isPGroup_pCoreIn _ _
  have hYOp : Y ⊓ Op = ⊥ := by
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hYr
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hOpp
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes hr hσ.p_prime).mpr hrp)
  obtain ⟨i, hYi⟩ := lemmaV43_ii hσ hII hJ h31 hN' h42 h46 h21 hQF hW hr hrW hYr hTY hYW
  have hYN : Y ≤ σ.N := le_N_of_le_Ns hσ hII hDY hYi
  have hxY : ∀ y ∈ Y, σ.x * y * σ.x⁻¹ = y := fun y hy => by
    rw [← (σ.mem_N_iff y).mp (hYN hy)]; group
  suffices hcomp : ∀ k : Fin 3, comp σ R k ⊆ Op by
    rw [Subgroup.commutator_le]
    intro ρ hρ t ht
    have hρ' : ρ ∈ (R : Set G) := hρ
    rw [Conjugacy.coe_eq_mul_comp hσ hRodd hTR] at hρ'
    obtain ⟨_, ⟨_, ⟨c, hc, u0, hu0, rfl⟩, u1, hu1, rfl⟩, u2, hu2, rfl⟩ := hρ'
    have ho : u0 * u1 * u2 ∈ Op :=
      Op.mul_mem (Op.mul_mem (hcomp 0 hu0) (hcomp 1 hu1)) (hcomp 2 hu2)
    have hct : t * c = c * t := (Subgroup.mem_centralizer_iff.mp hc.2) t ht
    set o := u0 * u1 * u2
    have hto : t * o⁻¹ * t⁻¹ ∈ Op :=
      (Subgroup.mem_normalizer_iff.mp (hTOp ht) _).mp (Op.inv_mem ho)
    have hcK : c ∈ K := (le_sup_left : R ≤ K) hc.1
    have e : ⁅c * u0 * u1 * u2, t⁆ = c * (o * (t * o⁻¹ * t⁻¹)) * c⁻¹ := by
      rw [commutatorElement_def]
      have hc' : t * c⁻¹ * t⁻¹ = c⁻¹ := by
        rw [show t * c⁻¹ * t⁻¹ = (t * c * t⁻¹)⁻¹ by group, hct]; group
      calc c * u0 * u1 * u2 * t * (c * u0 * u1 * u2)⁻¹ * t⁻¹ =
          c * (o * (t * o⁻¹ * t⁻¹)) * (t * c⁻¹ * t⁻¹) := by simp only [o]; group
        _ = c * (o * (t * o⁻¹ * t⁻¹)) * c⁻¹ := by rw [hc']
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hKOp hcK) _).mp (Op.mul_mem ho hto)
  set B : Subgroup G := K ⊔ σ.T with hBdef
  have hKB : K ≤ B := le_sup_left
  have hTB : σ.T ≤ B := le_sup_right
  have hRB : R ≤ B := le_sup_left.trans hKB
  have hYB : Y ≤ B := le_sup_right.trans hKB
  have hBOp : B ≤ Subgroup.normalizer (Op : Set G) := sup_le hKOp hTOp
  have : (Op.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hBOp
  set π := QuotientGroup.mk' (Op.subgroupOf B) with hπ
  set Kb := (K.subgroupOf B).map π with hKb
  set Yb := (Y.subgroupOf B).map π with hYb
  set Z := pCoreIn r Kb with hZ
  have hKbdvd : Nat.card Kb ∣ Nat.card R * Nat.card Y :=
    (card_map_subgroupOf_dvd hKB).trans hKdvd
  have hKbodd : Odd (Nat.card Kb) := (hRodd.mul hYodd).of_dvd_nat hKbdvd
  have hKbsolv : Group.IsSolvable Kb := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hKbodd
  have hprimes : ∀ q : ℕ, q.Prime → q ∣ Nat.card Kb → q = σ.p ∨ q = r := by
    intro q hq hqK
    rcases (Nat.Prime.dvd_mul hq).mp (hqK.trans hKbdvd) with h | h
    · obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hRp
      rw [ha] at h
      exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hσ.p_prime).mp (hq.dvd_of_dvd_pow h))
    · obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hYr
      rw [ha] at h
      exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow h))
  have hOpb : pCoreIn σ.p Kb = ⊥ := by
    set P' := pCoreIn σ.p Kb
    set Q : Subgroup G := K ⊓ (P'.comap π).map B.subtype with hQ
    have hQp : IsPGroup σ.p Q := by
      rintro ⟨g, hgK, ⟨b, hb, rfl⟩⟩
      obtain ⟨a, ha⟩ := (DataConstruction.isPGroup_pCoreIn σ.p Kb) ⟨π b, hb⟩
      have h1 : π (b ^ σ.p ^ a) = 1 := by
        have := congrArg Subtype.val ha
        simpa using this
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      obtain ⟨c, hc⟩ := hOpp ⟨_, h1⟩
      refine ⟨a + c, Subtype.ext ?_⟩
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_subtype] at this ⊢
      rw [pow_add, pow_mul]
      exact this
    have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro g
      have key : ∀ k ∈ K, ∀ g ∈ Q, k * g * k⁻¹ ∈ Q := by
        rintro k hk g ⟨hgK, ⟨b, hb, rfl⟩⟩
        refine ⟨K.mul_mem (K.mul_mem hk hgK) (K.inv_mem hk), ⟨⟨k, hKB hk⟩ * b * ⟨k, hKB hk⟩⁻¹,
          ?_, rfl⟩⟩
        have hkb : π ⟨k, hKB hk⟩ ∈ Kb := mk'_mem_map_subgroupOf hk (hKB hk)
        have hn := DataConstruction.le_normalizer_pCoreIn σ.p Kb hkb
        show π (⟨k, hKB hk⟩ * b * ⟨k, hKB hk⟩⁻¹) ∈ P'
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hn _).mp hb
      constructor
      · exact key k hk g
      · intro h
        have := key k⁻¹ (K.inv_mem hk) _ h
        simpa [mul_assoc] using this
    have hQOp : Q ≤ Op := DataConstruction.le_pCoreIn inf_le_left hKQ hQp
    rw [eq_bot_iff]
    intro γ hγ
    have hγK : γ ∈ Kb := pCoreIn_le σ.p Kb hγ
    obtain ⟨k, hk, rfl⟩ := (mem_map_subgroupOf_iff hKB).mp hγK
    have hkQ : k ∈ Q := ⟨hk, ⟨⟨k, hKB hk⟩, hγ, rfl⟩⟩
    rw [Subgroup.mem_bot, mk'_eq_one_iff]
    exact hQOp hkQ
  have hYbK : Yb ≤ Kb :=
    Subgroup.map_mono fun y hy => show (y : G) ∈ K from (le_sup_right : Y ≤ K) hy
  have hZY : Z ≤ Yb := by
    have hZr : IsPGroup r Z := DataConstruction.isPGroup_pCoreIn r Kb
    have hYbr : IsPGroup r Yb := hYr.comap_subtype.map _
    have hYbZ : Yb ≤ Subgroup.normalizer (Z : Set (↥B ⧸ Op.subgroupOf B)) :=
      hYbK.trans (DataConstruction.le_normalizer_pCoreIn r Kb)
    have hsup := IsPGroup.to_sup_of_normal_left' hZr hYbr hYbZ
    have hsupK : Z ⊔ Yb ≤ Kb := sup_le (pCoreIn_le r Kb) hYbK
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hsup
    have hcardYb : Nat.card Yb = Nat.card Y := card_map_subgroupOf_of_inf_eq_bot hYB hYOp
    have hdvd : r ^ a ∣ Nat.card Y := by
      have h1 : r ^ a ∣ Nat.card R * Nat.card Y :=
        ha ▸ (Subgroup.card_dvd_of_le hsupK).trans hKbdvd
      obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hRp
      rw [hb] at h1
      exact (Nat.Coprime.pow a b ((Nat.coprime_primes hr hσ.p_prime).mpr hrp)).dvd_of_dvd_mul_left
        h1
    have hle : Nat.card (Z ⊔ Yb : Subgroup _) ≤ Nat.card Yb := by
      rw [ha, hcardYb]
      exact Nat.le_of_dvd Nat.card_pos hdvd
    have heq : Yb = Z ⊔ Yb := Subgroup.eq_of_le_of_card_ge le_sup_right hle
    rw [heq]
    exact le_sup_left
  have hxB : σ.x ∈ B := hTB σ.x_mem_T
  have hx₂B : σ.x₂ ∈ B := hTB σ.x₂_mem_T
  have hsK : ∀ {t : G} (ht : t ∈ σ.T), π ⟨t, hTB ht⟩ ∈ Subgroup.normalizer (Kb : Set _) :=
    fun {t} ht => map_subgroupOf_le_normalizer (C := K) (A := σ.T) hTK
      (mk'_mem_map_subgroupOf ht (hTB ht))
  have hpel : ∀ u (hu : u ∈ R), ∃ k : ℕ, (π ⟨u, hRB hu⟩) ^ σ.p ^ k = 1 := by
    intro u hu
    obtain ⟨k, hk⟩ := hRp ⟨u, hu⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨u, hRB hu⟩ : B) ^ σ.p ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hinv_of_cent : ∀ {s : G} (hs : s ∈ σ.T), (∀ y ∈ Y, s * y * s⁻¹ = y) →
      ∀ u ∈ R, s * u * s⁻¹ = u⁻¹ → u ∈ Op := by
    intro s hs hsY u hu hsu
    obtain ⟨k, hk⟩ := hpel u hu
    have h := eq_one_of_conj_eq_inv_of_centralizes hKbsolv hprimes hOpb hKbodd
      (mk'_mem_map_subgroupOf ((le_sup_left : R ≤ K) hu) (hRB hu)) hk (s := π ⟨s, hTB hs⟩) ?_ ?_
    · exact (mk'_eq_one_iff (hRB hu)).mp h
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := (mem_map_subgroupOf_iff hYB).mp (hZY hz)
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hsY y hy)
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
      congr 1
      exact Subtype.ext hsu
  intro k
  fin_cases k
  ·
    intro u hu
    have hux : σ.x₂ * u * σ.x₂⁻¹ = u⁻¹ := hu.2.2
    by_cases hY0 : ∃ v ∈ comp σ Y 0, v ≠ 1
    ·
      have hW1 : ¬ W ≤ oddCoreIn (σ.Ns 0) := by
        intro h
        have hW1 : W ≠ ⊥ := by
          intro hb
          rw [hb, Subgroup.card_bot] at hrW
          exact hr.one_lt.ne' (Nat.eq_one_of_dvd_one hrW)
        apply hW1
        rw [eq_bot_iff, ← W_inf_ON hJ hW]
        exact le_inf le_rfl h
      obtain ⟨hcompO, hord, hinvr⟩ :=
        lemmaV43_i hσ hII hJ h31 hN' h42 h46 h21 hW hr hrW hYr hTY hYW hY0 hW1
      set A : Subgroup G := Y ⊓ σ.ON with hA
      have hAinvG : ∀ a ∈ A, σ.x₂ * a * σ.x₂⁻¹ = a⁻¹ := by
        have hTA : σ.T ≤ Subgroup.normalizer (A : Set G) :=
          (le_inf hTY ((σ.T_le_N hσ).trans σ.N_le_normalizer_ON)).trans
            Subgroup.inf_normalizer_le_normalizer_inf
        obtain ⟨R₀, hR₀, hAR₀, hTR₀⟩ := exists_isSylowOf_normalized_ge_of_odd hr (isPGroup_T hσ)
          ((σ.T_le_N hσ).trans σ.N_le_normalizer_ON) σ.odd_card_ON inf_le_right
          (hYr.to_le inf_le_left) hTA
        intro a ha
        exact (σ.centralized_or_inverted_of_T_invariant hσ hr hR₀ hTR₀).2 hinvr a (hAR₀ ha)
      set R₁ : Subgroup G := R ⊓ σ.N with hR₁
      have hR₁Y : (R₁ : Set G) * Y = Y * R₁ := by
        have hS2 : IsPGroup 2 (Subgroup.zpowers σ.x) := (isPGroup_T hσ).to_le
          ((Subgroup.zpowers_le).mpr σ.x_mem_T)
        have hSR : Subgroup.zpowers σ.x ≤ Subgroup.normalizer (R : Set G) :=
          (Subgroup.zpowers_le).mpr (hTR σ.x_mem_T)
        have hSY : Subgroup.zpowers σ.x ≤ Subgroup.normalizer (Y : Set G) :=
          (Subgroup.zpowers_le).mpr (hTY σ.x_mem_T)
        have hKcoe : (K : Set G) = (R : Set G) * Y := Omnibus.coe_sup_of_mul_comm hRY
        have hdec := centralizer_mul_of_mul_eq hKodd hS2 le_sup_left le_sup_right hSR hSY hKcoe
        have hcz : Subgroup.centralizer (Subgroup.zpowers σ.x : Set G) = σ.N := by
          rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
          rfl
        rw [hcz, inf_eq_left.mpr hYN] at hdec
        apply Set.Subset.antisymm
        · intro g hg
          have hg' : g⁻¹ ∈ ((K ⊓ σ.N : Subgroup G) : Set G) := by
            rw [SetLike.mem_coe]
            apply Subgroup.inv_mem
            rw [← SetLike.mem_coe, hdec]
            exact hg
          rw [hdec] at hg'
          obtain ⟨a, ha, b, hb, hab⟩ := hg'
          have hab' : a * b = g⁻¹ := hab
          refine ⟨b⁻¹, Y.inv_mem hb, a⁻¹, R₁.inv_mem ha, ?_⟩
          show b⁻¹ * a⁻¹ = g
          rw [← mul_inv_rev, hab', inv_inv]
        · rintro _ ⟨b, hb, a, ha, rfl⟩
          have hmem : b * a ∈ K ⊓ σ.N :=
            (K ⊓ σ.N).mul_mem ⟨(le_sup_right : Y ≤ K) hb, hYN hb⟩
              ⟨(le_sup_left : R ≤ K) ha.1, ha.2⟩
          have : b * a ∈ ((K ⊓ σ.N : Subgroup G) : Set G) := hmem
          rwa [hdec] at this
      have hcopR₁Y : Nat.Coprime (Nat.card R₁) (Nat.card Y) := by
        obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hRp.to_le (inf_le_left : R₁ ≤ R))
        obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hYr
        rw [ha, hb]
        exact Nat.Coprime.pow a b ((Nat.coprime_primes hσ.p_prime hr).mpr hpr)
      have hR₁A : (R₁ : Set G) * A = A * R₁ :=
        (permutable_inf_of_le_normalizer hR₁Y hcopR₁Y
          ((inf_le_right : R₁ ≤ σ.N).trans σ.N_le_normalizer_ON)).1
      have hAB : A ≤ B := inf_le_left.trans hYB
      have hR₁B : R₁ ≤ B := inf_le_left.trans hRB
      set Ab := (A.subgroupOf B).map π with hAb
      set R₁b := (R₁.subgroupOf B).map π with hR₁b
      have hR₁bK : R₁b ≤ Kb :=
        Subgroup.map_mono fun y hy => show (y : G) ∈ K from (le_sup_left : R ≤ K) hy.1
      have hR₁bp : IsPGroup σ.p R₁b := (hRp.to_le inf_le_left).comap_subtype.map _
      have hAbr : IsPGroup r Ab := (hYr.to_le inf_le_left).comap_subtype.map _
      have hR₁Ab := map_subgroupOf_mul_comm (M := Op) hR₁B hAB hR₁A
      have hx₂O : σ.x₂ ∉ Op := by
        intro h
        have h2 : orderOf σ.x₂ ∣ Nat.card Op := Subgroup.orderOf_dvd_natCard Op h
        rw [hσ.x₂_order] at h2
        exact (Nat.not_even_iff_odd.mpr (Omnibus.odd_card_of_isPGroup hσ.p_prime hσ.p_ne_two
          hOpp)) (even_iff_two_dvd.mpr h2)
      have hs2 : orderOf (π ⟨σ.x₂, hx₂B⟩) = 2 := by
        apply orderOf_eq_prime
        · rw [← map_pow]
          have : (⟨σ.x₂, hx₂B⟩ : B) ^ 2 = 1 := Subtype.ext (by
            simp only [Subgroup.coe_pow, Subgroup.coe_one]
            rw [← hσ.x₂_order, pow_orderOf_eq_one])
          rw [this, map_one]
        · intro h
          exact hx₂O ((mk'_eq_one_iff hx₂B).mp h)
      have hAinv : ∀ a ∈ Ab, π ⟨σ.x₂, hx₂B⟩ * a * (π ⟨σ.x₂, hx₂B⟩)⁻¹ = a⁻¹ := by
        intro γ hγ
        obtain ⟨a, ha, rfl⟩ := (mem_map_subgroupOf_iff hAB).mp hγ
        rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
        congr 1
        exact Subtype.ext (hAinvG a ha)
      have hZinv : ∀ z ∈ Z, π ⟨σ.x₂, hx₂B⟩ * z * (π ⟨σ.x₂, hx₂B⟩)⁻¹ = z⁻¹ → z ∈ Ab := by
        intro z hz hzinv
        obtain ⟨y, hy, rfl⟩ := (mem_map_subgroupOf_iff hYB).mp (hZY hz)
        rw [← map_inv, ← map_mul, ← map_mul, ← map_inv] at hzinv
        have hyY : σ.x₂ * y * σ.x₂⁻¹ ∈ Y :=
          (Subgroup.mem_normalizer_iff.mp (hTY σ.x₂_mem_T) y).mp hy
        have h1 := (mk'_eq_mk'_iff (B.mul_mem (B.mul_mem hx₂B (hYB hy)) (B.inv_mem hx₂B))
          (B.inv_mem (hYB hy))).mp hzinv
        have h2 : (σ.x₂ * y * σ.x₂⁻¹)⁻¹ * y⁻¹ ∈ Y ⊓ Op :=
          ⟨Y.mul_mem (Y.inv_mem hyY) (Y.inv_mem hy), h1⟩
        rw [hYOp, Subgroup.mem_bot] at h2
        have hinv : σ.x₂ * y * σ.x₂⁻¹ = y⁻¹ := by
          have := inv_eq_of_mul_eq_one_right h2
          rwa [inv_inv] at this
        have hyc : y ∈ comp σ Y 0 := by
          refine ⟨hy, ?_, hinv⟩
          exact ((σ.mem_N_iff y).mp (hYN hy)).symm
        exact mk'_mem_map_subgroupOf (Subgroup.mem_inf.mpr ⟨hy, hcompO hyc⟩) (hYB hy)
      have hZA : Z ≤ Subgroup.normalizer (Ab : Set _) := by
        refine hZY.trans (map_subgroupOf_le_normalizer ?_)
        exact (le_inf Subgroup.le_normalizer (hYN.trans σ.N_le_normalizer_ON)).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have huR₁ : u ∈ R₁ := ⟨hu.1, (σ.mem_N_iff u).mpr hu.2.1.symm⟩
      have hsu : π ⟨σ.x₂, hx₂B⟩ * π ⟨u, hRB hu.1⟩ * (π ⟨σ.x₂, hx₂B⟩)⁻¹ =
          (π ⟨u, hRB hu.1⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
        congr 1
        exact Subtype.ext hux
      have h := eq_one_of_conj_eq_inv_of_permutable hpr hKbsolv hprimes hOpb hKbodd hR₁bK hR₁bp
        hAbr hR₁Ab hs2 (hsK σ.x₂_mem_T) hAinv hZinv hZA
        (mk'_mem_map_subgroupOf huR₁ (hRB hu.1)) hsu
      exact (mk'_eq_one_iff (hRB hu.1)).mp h
    ·
      push Not at hY0
      have hx₂Y : ∀ y ∈ Y, σ.x₂ * y * σ.x₂⁻¹ = y := by
        intro y hy
        have hy' : y ∈ (Y : Set G) := hy
        rw [Conjugacy.coe_eq_mul_comp hσ hYodd hTY] at hy'
        obtain ⟨_, ⟨_, ⟨c, hc, v0, hv0, rfl⟩, v1, hv1, rfl⟩, v2, hv2, rfl⟩ := hy'
        have htriv : ∀ v ∈ Y, σ.x * v * σ.x⁻¹ = v⁻¹ → v = 1 := by
          intro v hv hvinv
          rw [hxY v hv] at hvinv
          have hodd : Odd (orderOf v) := hYodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hv)
          apply Omnibus.eq_one_of_sq_eq_one hodd
          rw [sq]
          calc v * v = v * v⁻¹ := by rw [← hvinv]
            _ = 1 := mul_inv_cancel v
        simp only [hY0 v0 hv0, htriv v1 hv1.1 (Conjugacy.conj_x_of_mem_comp_one hv1),
          htriv v2 hv2.1 (Conjugacy.conj_x_of_mem_comp_two hv2), mul_one]
        rw [(Subgroup.mem_centralizer_iff.mp hc.2) σ.x₂ σ.x₂_mem_T]
        group
      exact hinv_of_cent σ.x₂_mem_T hx₂Y u hu.1 hux
  · intro u hu
    exact hinv_of_cent σ.x_mem_T hxY u hu.1 (Conjugacy.conj_x_of_mem_comp_one hu)
  · intro u hu
    exact hinv_of_cent σ.x_mem_T hxY u hu.1 (Conjugacy.conj_x_of_mem_comp_two hu)

end CFSG.ABGTheoremB.V4
