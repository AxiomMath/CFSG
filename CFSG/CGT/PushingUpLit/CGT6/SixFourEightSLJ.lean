module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightSLPkg
public import CFSG.CGT.PushingUpLit.EightOneWindowBasic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem EightCtx.mem_sup_R_of_act {Y R : Subgroup G} {T : Sylow 2 G} (h : EightCtx Y T R)
    (hC : Y ⊓ Subgroup.centralizer (blockU Y : Set G) = oTwoIn Y) {j y : G}
    (hj : j ∈ (T : Subgroup G)) (hjN : j ∈ Subgroup.normalizer (Y : Set G)) (hy : y ∈ Y)
    (hact : ∀ u ∈ blockU Y, j * u * j⁻¹ = y * u * y⁻¹) : j ∈ Y ⊔ R := by
  classical
  have hRn := h.hRn
  have hOR : oTwoIn Y ≤ R := h.le_R_of_le_centralizerModCore
    (ThreeFromEight.isPGroup_oTwoIn Y) (EightOneWindow.oTwoIn_le_centralizerModCore Y)
  have hyN : y ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hy
  have hyU : y ∈ Subgroup.normalizer (blockU Y : Set G) := normalizer_le_normalizer_blockU Y hyN
  have hjU : j ∈ Subgroup.normalizer (blockU Y : Set G) := normalizer_le_normalizer_blockU Y hjN
  set c : G := y⁻¹ * j with hc
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) := mul_mem (inv_mem hyN) hjN
  have hcU : c ∈ Subgroup.centralizer (blockU Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := hact u hu
    calc u * c = u * (y⁻¹ * j) := rfl
      _ = y⁻¹ * (y * u * y⁻¹) * j := by group
      _ = y⁻¹ * (j * u * j⁻¹) * j := by rw [h1]
      _ = c * u := by rw [hc]; group
  have hcC : c ∈ centralizerModCore Y :=
    EightCtx.mem_centralizerModCore_of_centralizer_blockU hC hcN hcU
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨j, hj⟩
  have hjk : j ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hconj : conjAct (blockU Y) ⟨y, hyU⟩ = conjAct (blockU Y) ⟨j, hjU⟩ := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [conjAct_apply', conjAct_apply']
    exact (hact u u.2).symm
  have hyk : y ^ 2 ^ k ∈ Subgroup.centralizer (blockU Y : Set G) := by
    rw [← conjAct_eq_one_iff (blockU Y) ⟨y ^ 2 ^ k, Subgroup.pow_mem _ hyU _⟩]
    have e1 : (⟨y ^ 2 ^ k, Subgroup.pow_mem _ hyU _⟩ :
        ↥(Subgroup.normalizer (blockU Y : Set G))) = ⟨y, hyU⟩ ^ 2 ^ k := rfl
    have e2 : (⟨j ^ 2 ^ k, Subgroup.pow_mem _ hjU _⟩ :
        ↥(Subgroup.normalizer (blockU Y : Set G))) = ⟨j, hjU⟩ ^ 2 ^ k := rfl
    have e3 : (⟨j ^ 2 ^ k, Subgroup.pow_mem _ hjU _⟩ :
        ↥(Subgroup.normalizer (blockU Y : Set G))) = 1 := Subtype.ext hjk
    rw [e1, map_pow, hconj, ← map_pow, ← e2, e3, map_one]
  have hyO : y ^ 2 ^ k ∈ oTwoIn Y := by
    rw [← hC]
    exact Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ hy _, hyk⟩
  obtain ⟨l, hl⟩ := exists_pow_eq_one_of_mem_oTwoIn hyO
  have hy2 : y ^ 2 ^ (k + l) = 1 := by rw [pow_add, pow_mul]; exact hl
  have hj2 : j ^ 2 ^ (k + l) = 1 := by rw [pow_add, pow_mul, hjk, one_pow]
  let π : G →* G ⧸ R := QuotientGroup.mk' R
  have hcomm : Commute (π y) (π c) := by
    have h1 : (y * c)⁻¹ * (c * y) ∈ R := by
      have := hOR ((inv_mem hcC : c⁻¹ ∈ centralizerModCore Y).2 y⁻¹ (inv_mem hy))
      have e : ⁅c⁻¹, y⁻¹⁆ = (y * c)⁻¹ * (c * y) := by
        simp only [commutatorElement_def]
        group
      rw [← e]
      exact this
    show π y * π c = π c * π y
    rw [← map_mul, ← map_mul]
    exact QuotientGroup.eq.mpr h1
  have hjπ : π j = π y * π c := by rw [← map_mul, hc]; congr 1; group
  have hcomm' : Commute (π y) (π j) := by rw [hjπ]; exact (Commute.refl _).mul_right hcomm
  have hcpow : c ^ 2 ^ (k + l) ∈ R := by
    have : π (c ^ 2 ^ (k + l)) = 1 := by
      have e : π c = (π y)⁻¹ * π j := by rw [hjπ]; group
      rw [map_pow, e, Commute.mul_pow (hcomm'.inv_left), inv_pow, ← map_pow, ← map_pow, hy2, hj2,
        map_one]
      simp
    exact (QuotientGroup.eq_one_iff _).mp this
  have hcR : c ∈ R := mem_of_pow_mem_of_commutator_mem h.hNo h.hR (fun y' hy' => hOR (hcC.2 y' hy'))
    hcpow
  have : j = y * c := by rw [hc]; group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hcR)

theorem eight_sl_J {Y R : Subgroup G} {T : Sylow 2 G} (h : EightCtx Y T R) {n : ℕ} (hn : 1 ≤ n)
    (hnat : IsNaturalSLTwoModule ↥Y n) :
    ∃ A : Subgroup G, IsMaxElemAbelian (T : Subgroup G) A ∧ ¬ A ≤ centralizerModCore Y ∧
      jIn (T : Subgroup G) ≤ A ⊔ R ∧ jIn (T : Subgroup G) ≤ Y ⊔ R ∧
      (A ⊓ R).relIndex A = Nat.card (GaloisField 2 n) ∧
      (∀ x ∈ jIn (T : Subgroup G), x ∉ R → omegaOneCenterIn R ⊓ Subgroup.centralizer ({x} : Set G) =
        omegaOneCenterIn R ⊓ Subgroup.centralizer (jIn (T : Subgroup G) : Set G)) ∧
      (∀ x ∈ jIn (T : Subgroup G), ∀ v ∈ omegaOneCenterIn R,
        ⁅x, v⁆ ∈ Subgroup.centralizer (jIn (T : Subgroup G) : Set G)) := by
  classical
  have hRn := h.hRn
  have hC : Y ⊓ Subgroup.centralizer (blockU Y : Set G) = oTwoIn Y :=
    inf_centralizer_blockU_eq_SL h.hY.1 hnat
  obtain ⟨𝔘, h𝔘Y, hmain⟩ := eight_sl_main h hn hnat
  obtain ⟨A, hA, hnot⟩ := h.exists_isMax_not_le
  obtain ⟨hAeq, hrel, -, -, hP3, hP4⟩ := hmain A hA hnot
  have hAT : A ≤ (T : Subgroup G) := hA.1
  have hJdef : ∀ B, IsMaxElemAbelian (T : Subgroup G) B → B ≤ jIn (T : Subgroup G) := by
    intro B hB
    rw [jIn_eq_thompsonJ]
    exact le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) B hB
  have hVR : ∀ r ∈ R, ∀ v ∈ omegaOneCenterIn R, r * v = v * r := fun r hr v hv =>
    (mem_omegaOneCenterIn_iff.mp hv).2.1 r hr
  have hB : ∀ B, IsMaxElemAbelian (T : Subgroup G) B →
      B ≤ R ∨ (¬ B ≤ centralizerModCore Y ∧ autOn B (blockU Y) = 𝔘) := by
    intro B hBm
    by_cases hBC : B ≤ centralizerModCore Y
    · exact Or.inl (h.le_R_of_le_centralizerModCore (isPGroup_two_of_isElemAbelian hBm.2.1) hBC)
    · exact Or.inr ⟨hBC, (hmain B hBm hBC).1⟩
  have hJA : jIn (T : Subgroup G) ≤ A ⊔ R := by
    rw [jIn_eq_thompsonJ]
    refine iSup₂_le fun B hBm => ?_
    rcases hB B hBm with hBR | ⟨hBC, hBeq⟩
    · exact hBR.trans le_sup_right
    · intro b hb
      have hbN : b ∈ Subgroup.normalizer (Y : Set G) := h.le_normalizer_of_isMax hBm hb
      have hbU : b ∈ Subgroup.normalizer (blockU Y : Set G) := normalizer_le_normalizer_blockU Y hbN
      have hmem : conjAct (blockU Y) ⟨b, hbU⟩ ∈ autOn A (blockU Y) := by
        rw [hAeq, ← hBeq]
        exact mem_autOn_iff.mpr ⟨⟨b, hbU⟩, hb, rfl⟩
      obtain ⟨a, haA, hab⟩ := mem_autOn_iff.mp hmem
      have haN : (a : G) ∈ Subgroup.normalizer (Y : Set G) := h.le_normalizer_of_isMax hA haA
      have hc : (a : G)⁻¹ * b ∈ Subgroup.centralizer (blockU Y : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have h1 := congrArg (fun φ : MulAut ↥(blockU Y) => ((φ ⟨u, hu⟩ : ↥(blockU Y)) : G)) hab
        simp only [conjAct_apply'] at h1
        calc u * ((a : G)⁻¹ * b) = (a : G)⁻¹ * ((a : G) * u * (a : G)⁻¹) * b := by group
          _ = (a : G)⁻¹ * (b * u * b⁻¹) * b := by rw [h1]
          _ = ((a : G)⁻¹ * b) * u := by group
      have hcC : (a : G)⁻¹ * b ∈ centralizerModCore Y :=
        EightCtx.mem_centralizerModCore_of_centralizer_blockU hC
          (mul_mem (inv_mem haN) hbN) hc
      have hcT : (a : G)⁻¹ * b ∈ (T : Subgroup G) := mul_mem (inv_mem (hAT haA)) (hBm.1 hb)
      have hcR : (a : G)⁻¹ * b ∈ R := by
        have hP2 : IsPGroup 2 (Subgroup.zpowers ((a : G)⁻¹ * b)) :=
          T.isPGroup'.to_le (Subgroup.zpowers_le.mpr hcT)
        exact h.le_R_of_le_centralizerModCore hP2 (Subgroup.zpowers_le.mpr hcC)
          (Subgroup.mem_zpowers _)
      have : b = (a : G) * ((a : G)⁻¹ * b) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haA) (Subgroup.mem_sup_right hcR)
  have hJY : jIn (T : Subgroup G) ≤ Y ⊔ R := by
    rw [jIn_eq_thompsonJ]
    refine iSup₂_le fun B hBm => ?_
    rcases hB B hBm with hBR | ⟨hBC, hBeq⟩
    · exact hBR.trans le_sup_right
    · intro b hb
      have hbN : b ∈ Subgroup.normalizer (Y : Set G) := h.le_normalizer_of_isMax hBm hb
      have hbU : b ∈ Subgroup.normalizer (blockU Y : Set G) := normalizer_le_normalizer_blockU Y hbN
      have hmem : conjAct (blockU Y) ⟨b, hbU⟩ ∈ autOn Y (blockU Y) := by
        refine h𝔘Y ?_
        rw [← hBeq]
        exact mem_autOn_iff.mpr ⟨⟨b, hbU⟩, hb, rfl⟩
      obtain ⟨y, hyY, hyb⟩ := mem_autOn_iff.mp hmem
      refine h.mem_sup_R_of_act hC (hBm.1 hb) hbN hyY ?_
      intro u hu
      have h1 := congrArg (fun φ : MulAut ↥(blockU Y) => ((φ ⟨u, hu⟩ : ↥(blockU Y)) : G)) hyb
      simp only [conjAct_apply'] at h1
      exact h1.symm
  have hCVJ : omegaOneCenterIn R ⊓ Subgroup.centralizer (jIn (T : Subgroup G) : Set G) =
      omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (hJdef A hA))
    · intro v hv
      obtain ⟨hvV, hvA⟩ := Subgroup.mem_inf.mp hv
      refine Subgroup.mem_inf.mpr ⟨hvV, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      obtain ⟨a, haA, r, hrR, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hJA hx)
      have h1 : a * v = v * a := Subgroup.mem_centralizer_iff.mp hvA a haA
      have h2 : r * v = v * r := hVR r hrR v hvV
      calc a * r * v = a * (v * r) := by rw [mul_assoc, h2]
        _ = (a * v) * r := by group
        _ = (v * a) * r := by rw [h1]
        _ = v * (a * r) := by group
  refine ⟨A, hA, hnot, hJA, hJY, hrel, ?_, ?_⟩
  · intro x hx hxR
    obtain ⟨a, haA, r, hrR, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hJA hx)
    have haR : a ∉ R := fun haR => hxR (Subgroup.mul_mem _ haR hrR)
    rw [hCVJ, ← hP3 a haA haR]
    ext v
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq]
    constructor
    · rintro ⟨hvV, hv⟩
      refine ⟨hvV, ?_⟩
      have h2 : r * v = v * r := hVR r hrR v hvV
      have e1 : (a * r) * v = (a * v) * r := by rw [mul_assoc, h2, ← mul_assoc]
      have e2 : v * (a * r) = (v * a) * r := by rw [mul_assoc]
      exact mul_right_cancel (e1.symm.trans (hv.trans e2))
    · rintro ⟨hvV, hv⟩
      refine ⟨hvV, ?_⟩
      have h2 : r * v = v * r := hVR r hrR v hvV
      have e1 : (a * r) * v = (a * v) * r := by rw [mul_assoc, h2, ← mul_assoc]
      have e2 : v * (a * r) = (v * a) * r := by rw [mul_assoc]
      rw [e1, e2, hv]
  · intro x hx v hv
    obtain ⟨a, haA, r, hrR, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hJA hx)
    have h1 : ⁅a * r, v⁆ = ⁅a, v⁆ := by
      have h2 : r * v * r⁻¹ = v := by rw [hVR r hrR v hv]; group
      simp only [commutatorElement_def]
      calc a * r * v * (a * r)⁻¹ * v⁻¹ = a * (r * v * r⁻¹) * a⁻¹ * v⁻¹ := by group
        _ = a * v * a⁻¹ * v⁻¹ := by rw [h2]
    rw [h1]
    have hVn : (omegaOneCenterIn R).Normal := h.V_normal
    have hmemV : ⁅a, v⁆ ∈ omegaOneCenterIn R := by
      have e : ⁅a, v⁆ = (a * v * a⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact Subgroup.mul_mem _ (hVn.conj_mem v hv a) (Subgroup.inv_mem _ hv)
    have : ⁅a, v⁆ ∈ omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G) :=
      Subgroup.mem_inf.mpr ⟨hmemV, hP4 a haA v hv⟩
    rw [← hCVJ] at this
    exact this.2

end CFSG.CGT.PushingUpLit.CGT6
