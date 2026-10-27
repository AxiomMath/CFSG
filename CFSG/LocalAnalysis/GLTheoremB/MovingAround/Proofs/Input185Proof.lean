module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12a
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input185

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input185Proof

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Bar

variable {X : Type} [Group X] [Finite X]

theorem star_of_I710 (h : Input185.Input7_10_1) {p : ℕ} [hp : Fact p.Prime]
    (hX : CFSG.Open.IsKGroup X) (hO : GLAPPrimeCore p X = ⊥) {S : Subgroup X}
    (hS : CFSG.Open.fusionIsSylowIn p S ⊤) {g : X}
    (hg : g ∈ Subgroup.centralizer
      ((S ⊓ (Lemma114Layer.layerOf X ⊔ CFSG.pCore p X) : Subgroup X) : Set X))
    (hgp : ¬ p ∣ orderOf g) :
    g ∈ Lemma114Layer.layerOf X ⊔
      GLAPPrimeCoreOf p (Subgroup.centralizer ((S ⊓ Lemma114Layer.layerOf X : Subgroup X) : Set X)) := by
  have hTsub : (S ⊓ Lemma114Layer.layerOf X) ⊔ CFSG.pCore p X ≤
      S ⊓ (Lemma114Layer.layerOf X ⊔ CFSG.pCore p X) :=
    sup_le (inf_le_inf_left S le_sup_left)
      (le_inf (Input185.pCore_le_of_fusionSylow hS) le_sup_right)
  have hgH : g ∈ Input185.H2set p S :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hTsub) hg
  have hgM : g ∈ Input185.Mset p S := Input185.mem_Mset_of_pprime h hX hO hS hgH hgp
  obtain ⟨C, hCM, hCD, hcop, hiv⟩ := Input185.exists_C_of_Mset h hX hO hS
  have hgC : g ∈ C := hiv g hgM hgp
  have hCDle : C ≤ Input185.Dset S := fun c hc =>
    Input185.H2set_le_Dset (p := p) S (Input185.mem_Mset_iff.1 (hCM hc)).1
  have hDN : Input185.Dset S ≤ Subgroup.normalizer (C : Set X) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact hCD d hd c hc
    · intro hc
      have hthis := hCD d⁻¹ (Subgroup.inv_mem _ hd) _ hc
      have e : d⁻¹ * (d * c * d⁻¹) * d⁻¹⁻¹ = c := by group
      rw [e] at hthis
      exact hthis
  exact Subgroup.mem_sup_right (Lemma114Layer.le_glaPPrimeCoreOf_of_normal' hCDle hDN hcop hgC)

theorem centralizer_le_layerJoin (h : Input185.Input7_10_1) {p : ℕ} [hp : Fact p.Prime]
    (hK : CFSG.Open.IsKGroup X) (hO : GLAPPrimeCore p X = ⊥) :
    ∀ n : ℕ, ∀ B : Subgroup X, IsPGroup p B → Nat.card X - Nat.card B = n →
      GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ≤ Input185.layerJoin p X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hB hn
  obtain ⟨S, hBS⟩ := IsPGroup.exists_le_sylow hB
  have hSsyl : CFSG.Open.fusionIsSylowIn p (S : Subgroup X) ⊤ :=
    ⟨le_top, S.isPGroup', fun P _ hP hle => S.is_maximal' hP hle⟩
  haveI : (Lemma114Layer.layerOf X).Normal := Lemma114Layer.layerOf_normal
  haveI : (CFSG.pCore p X).Normal := CFSG.pCore_normal (p := p) (G := X)
  have hYn : (Lemma114Layer.layerOf X ⊔ CFSG.pCore p X).Normal := Subgroup.sup_normal _ _
  haveI := hYn
  set Y : Subgroup X := Lemma114Layer.layerOf X ⊔ CFSG.pCore p X with hYdef
  set T : Subgroup X := (S : Subgroup X) ⊓ Y with hTdef
  have hBN : B ≤ Subgroup.normalizer (T : Set X) := by
    refine Lemma114Layer.le_normalizer_of_conj fun w hw y hy => ?_
    obtain ⟨hyS, hyY⟩ := Subgroup.mem_inf.1 hy
    exact Subgroup.mem_inf.2 ⟨(S : Subgroup X).mul_mem ((S : Subgroup X).mul_mem (hBS hw) hyS)
      ((S : Subgroup X).inv_mem (hBS hw)), hYn.conj_mem y hyY w⟩
  have hBT : ∀ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ ∈ T := fun b hb t ht =>
    (Subgroup.mem_normalizer_iff.1 (hBN hb) t).1 ht
  have hTp : IsPGroup p (T : Subgroup X) := (S.isPGroup').to_le inf_le_left
  have hTS : (T : Subgroup X) ≤ (S : Subgroup X) := inf_le_left
  have hTY : (T : Subgroup X) ≤ Y := inf_le_right
  set Q : Subgroup X := T ⊓ Subgroup.normalizer (B : Set X) with hQdef
  have hQp : IsPGroup p Q := hTp.to_le inf_le_left
  have hQT : Q ≤ T := inf_le_left
  have hQN : ∀ q ∈ Q, q ∈ Subgroup.normalizer (B : Set X) := fun q hq => (Subgroup.mem_inf.1 hq).2
  by_cases hQB : Q ≤ B
  ·
    let H : Subgroup X :=
      { carrier := {y | ∃ b ∈ B, ∃ t ∈ T, y = b * t}
        mul_mem' := by
          rintro _ _ ⟨b1, hb1, t1, ht1, rfl⟩ ⟨b2, hb2, t2, ht2, rfl⟩
          exact ⟨b1 * b2, B.mul_mem hb1 hb2, b2⁻¹ * t1 * b2⁻¹⁻¹ * t2,
            T.mul_mem (hBT b2⁻¹ (B.inv_mem hb2) t1 ht1) ht2, by group⟩
        one_mem' := ⟨1, B.one_mem, 1, T.one_mem, by group⟩
        inv_mem' := by
          rintro _ ⟨b, hb, t, ht, rfl⟩
          exact ⟨b⁻¹, B.inv_mem hb, b * t⁻¹ * b⁻¹, hBT b hb t⁻¹ (T.inv_mem ht), by group⟩ }
    have hHS : H ≤ (S : Subgroup X) := by
      rintro _ ⟨b, hb, t, ht, rfl⟩
      exact (S : Subgroup X).mul_mem (hBS hb) (hTS ht)
    have hBH : B ≤ H := fun b hb => ⟨b, hb, 1, T.one_mem, by group⟩
    have hHB : H ≤ B := CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18.pgroup_normalizer_strict
      (S.isPGroup'.to_le hHS) hBH (by
      rintro y ⟨b, hb, t, ht, rfl⟩ hyN
      have htN : t ∈ Subgroup.normalizer (B : Set X) := by
        have h1 := (Subgroup.normalizer (B : Set X)).mul_mem
          ((Subgroup.normalizer (B : Set X)).inv_mem (Subgroup.le_normalizer hb)) hyN
        simpa using h1
      exact B.mul_mem hb (hQB (Subgroup.mem_inf.2 ⟨ht, htN⟩)))
    have hTB : (T : Subgroup X) ≤ B := fun t ht => hHB ⟨1, B.one_mem, t, ht, by group⟩
    have hDT : GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ≤
        Subgroup.centralizer (T : Set X) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact (Subgroup.mem_centralizer_iff.1
        (CFSG.LocalAnalysis.GLTheoremA.lstar_glaPPrimeCoreOf_le p _ hx)) t (hTB ht)
    have hSE : CFSG.Open.fusionIsSylowIn p ((S : Subgroup X) ⊓ Lemma114Layer.layerOf X)
        (Lemma114Layer.layerOf X) :=
      CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18.fusion_inf_normal hSsyl le_top inferInstance
    have hDS := Input185.pPrimeCore_centralizer_le_of_sylow (p := p)
      (show IsSylowIn p (Lemma114Layer.layerOf X) ((S : Subgroup X) ⊓ Lemma114Layer.layerOf X) from hSE)
    intro x hx
    have hxp : ¬ p ∣ orderOf x := Lemma114Layer.not_dvd_orderOf_of_mem_glaPPrimeCoreOf hx
    have hxmem := star_of_I710 h hK hO hSsyl (hDT hx) hxp
    have hEJ : Lemma114Layer.layerOf X ⊔ GLAPPrimeCoreOf p
        (Subgroup.centralizer (((S : Subgroup X) ⊓ Lemma114Layer.layerOf X : Subgroup X) : Set X)) ≤
          Input185.layerJoin p X := sup_le le_sup_left hDS
    exact hEJ hxmem
  ·
    set R : Subgroup X := Q ⊔ B with hRdef
    have hRS : R ≤ (S : Subgroup X) := sup_le (hQT.trans hTS) hBS
    have hRp : IsPGroup p R := S.isPGroup'.to_le hRS
    have hBR : B < R := lt_of_le_of_ne le_sup_right (fun h => hQB (le_sup_left.trans (le_of_eq h.symm)))
    have hcardlt : Nat.card B < Nat.card R := Subgroup.card_lt_of_lt hBR
    have hcardle : Nat.card R ≤ Nat.card X := Subgroup.card_le_card_group _
    have hIH := ih (Nat.card X - Nat.card R) (by omega) R hRp rfl
    refine CFSG.LocalAnalysis.GLTheoremA.lstar_coprime_criterion (Q := Q)
      (D := GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X))) (N := Input185.layerJoin p X) hQp
      (Lemma114Layer.coprime_card_glaPPrimeCoreOf _)
      (fun q hq => CFSG.LocalAnalysis.GLTheoremA.lstar_normalizer_centralizer (hQN q hq)) ?_ ?_
    ·
      intro d hd q hq
      have hqY : q ∈ Y := hTY (hQT hq)
      have hqN := CFSG.LocalAnalysis.GLTheoremA.lstar_normalizer_centralizer (p := p) (hQN q hq)
      have hqd := (Subgroup.mem_normalizer_iff.1 hqN d).1 hd
      have hz : d⁻¹ * (q * d * q⁻¹) ∈ GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) :=
        (GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X))).mul_mem
          ((GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X))).inv_mem hd) hqd
      have h1 : d⁻¹ * q * d⁻¹⁻¹ ∈ Y := hYn.conj_mem q hqY d⁻¹
      have hzY : d⁻¹ * (q * d * q⁻¹) ∈ Y := by
        have e : d⁻¹ * (q * d * q⁻¹) = (d⁻¹ * q * d⁻¹⁻¹) * q⁻¹ := by group
        rw [e]
        exact Y.mul_mem h1 (Y.inv_mem hqY)
      have hmem := Input185.pPrime_mem_layer_of_mem_sup hzY
        (Lemma114Layer.not_dvd_orderOf_of_mem_glaPPrimeCoreOf hz)
      have hEJ : Lemma114Layer.layerOf X ≤ Input185.layerJoin p X := le_sup_left
      exact hEJ hmem
    ·
      intro x hx hxQ
      have hxC : x ∈ Subgroup.centralizer (B : Set X) :=
        CFSG.LocalAnalysis.GLTheoremA.lstar_glaPPrimeCoreOf_le p _ hx
      have hxR : R ≤ Subgroup.centralizer ({x} : Set X) := by
        refine sup_le (fun q hq => Subgroup.mem_centralizer_singleton_iff.2 ?_)
          (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 ?_)
        · exact hxQ q hq
        · exact Subgroup.mem_centralizer_iff.1 hxC b hb
      have hxA : x ∈ Subgroup.centralizer (R : Set X) :=
        Subgroup.mem_centralizer_iff.2 fun r hr => Subgroup.mem_centralizer_singleton_iff.1 (hxR hr)
      have hAB : Subgroup.centralizer (R : Set X) ≤ Subgroup.centralizer (B : Set X) :=
        Subgroup.centralizer_le (fun b hb => Subgroup.mem_sup_right hb)
      have hNA : ∀ g ∈ Subgroup.centralizer (R : Set X),
          ∀ n ∈ GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ⊓ Subgroup.centralizer (R : Set X),
            g * n * g⁻¹ ∈
              GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ⊓ Subgroup.centralizer (R : Set X) := by
        intro g hg n hn
        obtain ⟨hnD, hnA⟩ := Subgroup.mem_inf.1 hn
        refine Subgroup.mem_inf.2 ⟨?_, Input185.conj_mem_centralizer hg hnA⟩
        have hgN := CFSG.LocalAnalysis.GLTheoremA.lstar_normalizer_centralizer (p := p)
          (Subgroup.centralizer_le_normalizer _ (hAB hg))
        exact (Subgroup.mem_normalizer_iff.1 hgN n).1 hnD
      have hANorm : Subgroup.centralizer (R : Set X) ≤ Subgroup.normalizer
          ((GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ⊓ Subgroup.centralizer (R : Set X) :
            Subgroup X) : Set X) :=
        Lemma114Layer.le_normalizer_of_conj fun g hg n hn => hNA g hg n hn
      have hsub : IsSubnormal
          (GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ⊓ Subgroup.centralizer (R : Set X))
          (Subgroup.centralizer (R : Set X)) :=
        IsSubnormal.step inf_le_right
          ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).2 hANorm) (IsSubnormal.refl _)
      have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCoreOf p (Subgroup.centralizer (B : Set X)) ⊓
          Subgroup.centralizer (R : Set X))) :=
        Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
          (Lemma114Layer.coprime_card_glaPPrimeCoreOf _)
      have hN'D := CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18.le_glaPPrimeCoreOf_of_coprime
        hp.out hsub hcop
      exact hIH (hN'D (Subgroup.mem_inf.2 ⟨hx, hxA⟩))

end Bar

section Bridge

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowIn {p : ℕ} (L : Subgroup G) : ∃ Q : Subgroup G, IsSylowIn p L Q := by
  obtain ⟨Q, -, hQmax⟩ := (Set.toFinite {R : Subgroup G | R ≤ L ∧ IsPGroup p ↥R}).exists_le_maximal
    (a := ⊥) ⟨bot_le, IsPGroup.of_bot⟩
  exact ⟨Q, hQmax.1.1, hQmax.1.2, fun R' hR'L hR'p hQR' =>
    le_antisymm (hQmax.2 ⟨hR'L, hR'p⟩ hQR') hQR'⟩

theorem mk_mem_centralizer_barX {p : ℕ} {X Q : Subgroup G} {w : ↥X}
    (hw : (w : G) ∈ Subgroup.centralizer (Q : Set G)) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) w ∈
      Subgroup.centralizer ((barX p X Q : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hz
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hw (q : G) (Subgroup.mem_subgroupOf.1 hq))

theorem barX_core_centralizer_le {p : ℕ} [hp : Fact p.Prime] {X B : Subgroup G} (hBX : B ≤ X)
    (hB : IsPGroup p ↥B) :
    barX p X (GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer (B : Set G))) ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer ((barX p X B : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X))) := by
  set W := GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer (B : Set G)) with hW
  have hWC : W ≤ X ⊓ Subgroup.centralizer (B : Set G) := Lemma114Layer.glaPPrimeCoreOf_le_self p _
  have hWX : W ≤ X := hWC.trans inf_le_left
  have hWK : barX p X W ≤ Subgroup.centralizer ((barX p X B : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
      Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    exact mk_mem_centralizer_barX (hWC (Subgroup.mem_subgroupOf.1 hw)).2
  have hKN : Subgroup.centralizer ((barX p X B : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
      Set (↥X ⧸ GLAPPrimeCore p ↥X)) ≤
      Subgroup.normalizer ((barX p X W : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X)) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_centralizer_barX_le hp.out hBX hB).trans
      (barX_le_normalizer (Lemma114Layer.le_normalizer_glaPPrimeCoreOf p _))
  have hcop : Nat.Coprime p (Nat.card ↥(barX p X W)) :=
    Lemma114Full.l114f_coprime_barX hWX
      ((Nat.Prime.coprime_iff_not_dvd hp.out).1 (Lemma114Layer.coprime_card_glaPPrimeCoreOf _))
  exact Lemma114Layer.le_glaPPrimeCoreOf_of_normal' hWK hKN hcop

theorem core_centralizer_barX_le {p : ℕ} [hp : Fact p.Prime] {X Q : Subgroup G} (hQX : Q ≤ X)
    (hQ : IsPGroup p ↥Q) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ((barX p X Q : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X))) ≤
      barX p X (GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer (Q : Set G))) := by
  classical
  set Vb := GLAPPrimeCoreOf p (Subgroup.centralizer
    ((barX p X Q : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) : Set (↥X ⧸ GLAPPrimeCore p ↥X))) with hVb
  set H : Subgroup G := X ⊓ Subgroup.centralizer (Q : Set G) with hH
  set V : Subgroup G := H ⊓ (Vb.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map X.subtype
    with hV
  have hcopV : Nat.Coprime p (Nat.card ↥V) := by
    have hcard : Nat.card ↥(Vb.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X))) =
        Nat.card ↥(GLAPPrimeCore p ↥X) * Nat.card ↥Vb :=
      QuotientGroup.card_preimage_mk (GLAPPrimeCore p ↥X) (Vb : Set (↥X ⧸ GLAPPrimeCore p ↥X))
    have h1 : Nat.Coprime p
        (Nat.card ↥((Vb.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map X.subtype)) := by
      rw [Subgroup.card_map_of_injective X.subtype_injective, hcard]
      exact Nat.Coprime.mul_right (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥X))
        (Lemma114Layer.coprime_card_glaPPrimeCoreOf _)
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) h1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := by
    apply Lemma114Layer.le_normalizer_of_conj
    intro w hw y hy
    obtain ⟨hyH, y', hy', hyy'⟩ := hy
    refine ⟨H.mul_mem (H.mul_mem hw hyH) (H.inv_mem hw), ?_⟩
    refine ⟨⟨w, hw.1⟩ * y' * (⟨w, hw.1⟩ : ↥X)⁻¹, ?_, ?_⟩
    · show QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨w, hw.1⟩ * y' * (⟨w, hw.1⟩ : ↥X)⁻¹) ∈ Vb
      rw [map_mul, map_mul, map_inv]
      have hwc := mk_mem_centralizer_barX (p := p) (X := X) (Q := Q) (w := (⟨w, hw.1⟩ : ↥X)) hw.2
      exact (Subgroup.mem_normalizer_iff.1 (Lemma114Layer.le_normalizer_glaPPrimeCoreOf p _ hwc) _).1 hy'
    · rw [← hyy']
      simp
  have hVcore : V ≤ GLAPPrimeCoreOf p H :=
    Lemma114Layer.le_glaPPrimeCoreOf_of_normal' inf_le_left hHN hcopV
  intro z hz
  have hzC := Lemma114Layer.glaPPrimeCoreOf_le_self p _ hz
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_centralizer_barX_le hp.out hQX hQ hzC)
  exact Subgroup.mem_map.2 ⟨c, Subgroup.mem_subgroupOf.2
    (hVcore ⟨Subgroup.mem_subgroupOf.1 hc, c, hz, rfl⟩), rfl⟩

theorem isSylowIn_barX {p : ℕ} [hp : Fact p.Prime] {X L Q : Subgroup G} (hLX : L ≤ X)
    (hQ : IsSylowIn p L Q) : IsSylowIn p (barX p X L) (barX p X Q) := by
  classical
  have hmax : ∀ R : Subgroup ↥L, IsPGroup p ↥R → Q.subgroupOf L ≤ R → R = Q.subgroupOf L := by
    intro R hR hle
    have hRL : R.map L.subtype ≤ L := Subgroup.map_subtype_le R
    have hRp : IsPGroup p ↥(R.map L.subtype) :=
      hR.of_equiv (Subgroup.equivMapOfInjective R L.subtype L.subtype_injective)
    have hQR : Q ≤ R.map L.subtype := by
      intro q hq
      exact Subgroup.mem_map.2 ⟨⟨q, hQ.1 hq⟩, hle (Subgroup.mem_subgroupOf.2 hq), rfl⟩
    have heq : R.map L.subtype = Q := hQ.2.2 _ hRL hRp hQR
    apply le_antisymm
    · intro r hr
      exact Subgroup.mem_subgroupOf.2 (by rw [← heq]; exact Subgroup.mem_map.2 ⟨r, hr, rfl⟩)
    · intro r hr
      have hrY : (r : G) ∈ R.map L.subtype := by
        rw [heq]; exact Subgroup.mem_subgroupOf.1 hr
      obtain ⟨x, hx, hxr⟩ := Subgroup.mem_map.1 hrY
      have hxr' : x = r := Subtype.ext hxr
      rw [← hxr']; exact hx
  let S : Sylow p ↥L := ⟨Q.subgroupOf L, Lemma114Layer.isPGroup_subgroupOf_of_le hQ.2.1 hQ.1,
    fun {R} hR hle => hmax R hR hle⟩
  let S' : Sylow p ↥(barX p X L) := S.mapSurjective (barMap_surjective hLX)
  have hS'coe : (S' : Subgroup ↥(barX p X L)) = (Q.subgroupOf L).map (barMap p hLX) := rfl
  have hS'eq : (S' : Subgroup ↥(barX p X L)).map (barX p X L).subtype = barX p X Q := by
    rw [hS'coe]
    apply le_antisymm
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hw
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hLX l,
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hl), rfl⟩
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
      have hxL : (x : G) ∈ L := hQ.1 (Subgroup.mem_subgroupOf.1 hx)
      exact Subgroup.mem_map.2 ⟨barMap p hLX ⟨x, hxL⟩, Subgroup.mem_map.2 ⟨⟨x, hxL⟩,
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 hx), rfl⟩, rfl⟩
  refine ⟨Lemma114Full.l114f_barX_mono hQ.1,
    Lemma114Full.l114f_isPGroup_barX (hQ.1.trans hLX) hQ.2.1, ?_⟩
  intro R hRL hRp hQR
  have hR' : IsPGroup p ↥(R.subgroupOf (barX p X L)) :=
    Lemma114Layer.isPGroup_subgroupOf_of_le hRp hRL
  have hle : (S' : Subgroup ↥(barX p X L)) ≤ R.subgroupOf (barX p X L) := by
    intro w hw
    rw [Subgroup.mem_subgroupOf]
    apply hQR
    rw [← hS'eq]
    exact Subgroup.mem_map.2 ⟨w, hw, rfl⟩
  have heq : R.subgroupOf (barX p X L) = (S' : Subgroup ↥(barX p X L)) := S'.is_maximal' hR' hle
  rw [← hS'eq, ← heq, Subgroup.map_subgroupOf_eq_of_le hRL]

theorem layerOf_quot_eq {p : ℕ} (X : Subgroup G) :
    Lemma114Layer.layerOf (↥X ⧸ GLAPPrimeCore p ↥X) = barX p X (GLAPLayer p X) := by
  apply le_antisymm
  · refine sSup_le fun K hK => ?_
    obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq (p := p) X hK
    exact Lemma114Full.l114f_barX_mono (le_sSup hL : L ≤ GLAPLayer p X)
  · rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff
      (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_le p X)]
    refine sSup_le fun L hL => ?_
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff (hL : GLAPComponent p X L).1]
    exact le_sSup (hL : GLAPComponent p X L).2.2.1

theorem core_le_lstar (p : ℕ) (X : Subgroup G) : GLAPPrimeCoreOf p X ≤ Lstar p X := by
  unfold Lstar
  exact le_sup_left.trans le_sup_left

theorem layer_le_lstar (p : ℕ) (X : Subgroup G) : GLAPLayer p X ≤ Lstar p X := by
  unfold Lstar
  exact le_sup_right.trans le_sup_left

theorem sylowCore_le_lstar {p : ℕ} {X Q : Subgroup G} (hQ : IsSylowIn p (GLAPLayer p X) Q) :
    GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer (Q : Set G)) ≤ Lstar p X := by
  unfold Lstar
  exact (le_iSup₂_of_le (f := fun Q (_ : IsSylowIn p (GLAPLayer p X) Q) =>
    GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer (Q : Set G))) Q hQ le_rfl).trans le_sup_right

theorem layerJoin_le_barX_lstar {p : ℕ} [hp : Fact p.Prime] (X : Subgroup G) :
    Input185.layerJoin p (↥X ⧸ GLAPPrimeCore p ↥X) ≤ barX p X (Lstar p X) := by
  obtain ⟨Q₀, hQ₀⟩ := exists_isSylowIn (p := p) (GLAPLayer p X)
  have hLX : GLAPLayer p X ≤ X := CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_le p X
  have hQ₀X : Q₀ ≤ X := hQ₀.1.trans hLX
  have hQb : IsSylowIn p (Lemma114Layer.layerOf (↥X ⧸ GLAPPrimeCore p ↥X)) (barX p X Q₀) := by
    rw [layerOf_quot_eq]
    exact isSylowIn_barX hLX hQ₀
  refine (Input185.layer_join_sylow_eq hQb).le.trans (sup_le ?_ ?_)
  · rw [layerOf_quot_eq]
    exact Lemma114Full.l114f_barX_mono (layer_le_lstar p X)
  · exact (core_centralizer_barX_le hQ₀X hQ₀.2.1).trans
      (Lemma114Full.l114f_barX_mono (sylowCore_le_lstar hQ₀))

theorem core_centralizer_le_lstar (h : Input185.Input7_10_1) {p : ℕ} [hp : Fact p.Prime]
    {X B : Subgroup G} (hK : CFSG.Open.IsKGroup ↥X) (hBX : B ≤ X) (hB : IsPGroup p ↥B) :
    GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer (B : Set G)) ≤ Lstar p X := by
  have hKb : CFSG.Open.IsKGroup (↥X ⧸ GLAPPrimeCore p ↥X) :=
    Lemma114Full.isKGroup_quotient_pPrime hK
  have hOb : GLAPPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ :=
    glaPPrimeCore_quotient_eq_bot hp.out
  have hBb : IsPGroup p ↥(barX p X B) := Lemma114Full.l114f_isPGroup_barX hBX hB
  have h35 := centralizer_le_layerJoin h hKb hOb _ (barX p X B) hBb rfl
  have hchain := (barX_core_centralizer_le hBX hB).trans (h35.trans (layerJoin_le_barX_lstar X))
  intro x hx
  have hxX : x ∈ X := (Lemma114Layer.glaPPrimeCoreOf_le_self p _ hx).1
  have hmk : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨x, hxX⟩ : ↥X) ∈ barX p X (Lstar p X) :=
    hchain (Subgroup.mem_map.2 ⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩)
  have hsup := CFSG.HardMathSupport.Solomon.Coordinator.i183_mem_sup_of_mk_mem hmk
  exact (sup_le le_rfl (core_le_lstar p X)) hsup

theorem centralizer_sup_eq (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_right))
  · intro z hz
    obtain ⟨hzA, hzB⟩ := Subgroup.mem_inf.1 hz
    have hAz : A ≤ Subgroup.centralizer ({z} : Set G) := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hzA a ha)
    have hBz : B ≤ Subgroup.centralizer ({z} : Set G) := fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hzB b hb)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.1 (sup_le hAz hBz hb)

theorem lstar_inf_centralizer_le
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h : Input185.Input7_10_1) {p : ℕ} [hp : Fact p.Prime] {X Q : Subgroup G}
    (hK : CFSG.Open.IsKGroup ↥X) (hQX : Q ≤ X) (hQ : IsPGroup p ↥Q) :
    Lstar p (X ⊓ Subgroup.centralizer (Q : Set G)) ≤ Lstar p X := by
  have hA : GLAPLayer p (X ⊓ Subgroup.centralizer (Q : Set G)) ≤ Lstar p X :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_inf_centralizer_le hS hK hp.out hQX
      hQ).trans (layer_le_lstar p X)
  have hB : GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer (Q : Set G)) ≤ Lstar p X :=
    core_centralizer_le_lstar h hK hQX hQ
  have hC : ∀ R : Subgroup G,
      IsSylowIn p (GLAPLayer p (X ⊓ Subgroup.centralizer (Q : Set G))) R →
        GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer (Q : Set G) ⊓
          Subgroup.centralizer (R : Set G)) ≤ Lstar p X := by
    intro R hR
    have hRY : R ≤ X ⊓ Subgroup.centralizer (Q : Set G) :=
      hR.1.trans (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_le p _)
    have hRX : R ≤ X := hRY.trans inf_le_left
    have hcomm : ∀ a ∈ Q, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
      Subgroup.mem_centralizer_iff.1 (hRY hb).2 a ha
    have hBp : IsPGroup p ↥(Q ⊔ R) := Lemma114Layer.isPGroup_sup_of_commute hQ hR.2.1 hcomm
    have hBX : Q ⊔ R ≤ X := sup_le hQX hRX
    have hYR : X ⊓ Subgroup.centralizer (Q : Set G) ⊓ Subgroup.centralizer (R : Set G) =
        X ⊓ Subgroup.centralizer ((Q ⊔ R : Subgroup G) : Set G) := by
      rw [centralizer_sup_eq, inf_assoc]
    rw [hYR]
    exact core_centralizer_le_lstar h hK hBX hBp
  exact sup_le (sup_le hB hA) (iSup₂_le hC)

end Bridge

theorem input18_5_of_schreier_I710 (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h : Input185.Input7_10_1) : Sec12a.Input18_5 := by
  intro G _ _ p hp hKP X d hXne hdX hdp
  haveI : Fact p.Prime := ⟨hp⟩
  have hK : CFSG.Open.IsKGroup ↥X := isKGroup_of_isKProper hKP hXne
  have hcz : Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) =
      Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have key := lstar_inf_centralizer_le hS h hK (Subgroup.zpowers_le.2 hdX)
    (Lemma114Full.l114f_isPGroup_zpowers hdp)
  rwa [hcz] at key

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input185Proof
