module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchLevel2
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT2Kill
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2EnumSpec
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchAct
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchLevel1

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

theorem t1List_survivor {d : ℕ × ℕ × ℕ × Bool} (hd : d ∈ t1List) (hn : d.2.2.2 = false) :
    ∃ j, j < 8 ∧ d.1 = s2K j ∧ d.2.1 = s2M j ∧ d.2.2.1 = s2Z j := by
  revert hn
  revert hd
  revert d
  decide

theorem l2eSurv_all
    {j : ℕ} (hj : j < 8) :
    ∃ W, l2eSurvOK j W = true := by
  interval_cases j
  · exact l2eSurv_check_0
  · exact l2eSurv_check_1
  · exact l2eSurv_check_2
  · exact l2eSurv_check_3
  · exact l2eSurv_check_4
  · exact l2eSurv_check_5
  · exact l2eSurv_check_6
  · exact l2eSurv_check_7

theorem card_inv_S {S : Subgroup G}
    (e : S ≃* SModel) : Nat.card {s : S // (s : G) * s = 1 ∧ (s : G) ≠ 1} = 3839 := by
  have hb := s2Basic_check
  unfold s2BasicCheck at hb
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  have h1 := SModel.codeIso.length_kInv_filter sMul_zero_zero (fun _ => true)
  rw [List.filter_true, hb.1.2] at h1
  rw [h1]
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun s => ?_)
  show _ ↔ e s * e s = 1 ∧ e s ≠ 1 ∧ true = true
  have k1 : e s * e s = 1 ↔ (s : G) * s = 1 := by
    rw [← map_mul, MulEquiv.map_eq_one_iff, Subtype.ext_iff]; rfl
  have k2 : e s ≠ 1 ↔ (s : G) ≠ 1 := by
    rw [ne_eq, MulEquiv.map_eq_one_iff, ne_eq, Subtype.ext_iff]; rfl
  rw [k1, k2]
  simp

theorem card_ord4_S {S : Subgroup G}
    (e : S ≃* SModel) :
    Nat.card {s : S // (s : G) * s ≠ 1 ∧ (s : G) * s * ((s : G) * s) = 1} = 41216 := by
  have hb := s2Basic_check
  unfold s2BasicCheck at hb
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  have h1 := SModel.codeIso.length_kOrd4_filter sMul_zero_zero (fun _ => true)
  rw [List.filter_true, hb.2] at h1
  rw [h1]
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun s => ?_)
  show _ ↔ e s * e s ≠ 1 ∧ e s * e s * (e s * e s) = 1 ∧ true = true
  have k1 : e s * e s ≠ 1 ↔ (s : G) * s ≠ 1 := by
    rw [ne_eq, ← map_mul, MulEquiv.map_eq_one_iff, ne_eq, Subtype.ext_iff]; rfl
  have k2 : e s * e s * (e s * e s) = 1 ↔ (s : G) * s * ((s : G) * s) = 1 := by
    rw [← map_mul, ← map_mul, MulEquiv.map_eq_one_iff, Subtype.ext_iff]; rfl
  rw [k1, k2]
  simp

theorem fpCount_eq : fpCount = 128 := by
  have hb := s2Basic_check
  unfold s2BasicCheck at hb
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  exact hb.1.1

theorem step_mul {T : Subgroup G} {a y : G} (ha : a ∈ T) (hyN : y ∈ normalizer (T : Set G))
    (hyT : y ∉ T) (hy2 : y * y ∈ T) :
    a * y ∈ normalizer (T : Set G) ∧ a * y ∉ T ∧ a * y * (a * y) ∈ T := by
  refine ⟨mul_mem (le_normalizer ha) hyN, fun h => hyT ?_, ?_⟩
  · have : y = a⁻¹ * (a * y) := by group
    rw [this]; exact mul_mem (inv_mem ha) h
  · have e1 : a * y * (a * y) = a * (y * a * y⁻¹) * (y * y) := by group
    rw [e1]
    exact mul_mem (mul_mem ha ((mem_normalizer_iff.1 hyN a).1 ha)) hy2

theorem comm_of_gens
    {S T₁ : Subgroup G} (e : S ≃* SModel) {mul : ℕ → ℕ → ℕ} (Φ : CodeIso T₁ 131072 mul)
    (hST : S ≤ T₁) {y : G} (hyN : y ∈ normalizer (T₁ : Set G)) {ι : Array ℕ} {F : ℕ → ℕ}
    (hyS : ∀ s : S, Φ.f (conjEquiv hyN ⟨s, hST s.2⟩) = ι[F (e s).code]!) {c : T₁}
    (hc : ∀ g ∈ sGens, c * Φ.g ι[F g]! = Φ.g ι[F g]! * c) (g : T₁) (hg : y⁻¹ * g * y ∈ S) :
    c * g = g * c := by
  have key : ∀ a : SModel, c * conjEquiv hyN ⟨e.symm a, hST (e.symm a).2⟩ =
      conjEquiv hyN ⟨e.symm a, hST (e.symm a).2⟩ * c := by
    intro a
    refine SModel.codeIso.induction sMul_zero_zero sGens_lt sGen (P := fun a =>
      c * conjEquiv hyN ⟨e.symm a, hST (e.symm a).2⟩ =
        conjEquiv hyN ⟨e.symm a, hST (e.symm a).2⟩ * c) ?_ ?_ a
    · have h1 : (⟨(e.symm 1 : S), hST (e.symm 1).2⟩ : T₁) = 1 := by
        apply Subtype.ext
        simp
      rw [h1, map_one, mul_one, one_mul]
    · intro b hb g' hg'
      have hcode : (e (e.symm (SModel.codeIso.g g'))).code = g' := by
        rw [MulEquiv.apply_symm_apply]
        exact SModel.codeIso.f_g (sGens_lt g' hg')
      have hgen : conjEquiv hyN ⟨e.symm (SModel.codeIso.g g'), hST (e.symm _).2⟩ =
          Φ.g ι[F g']! := by
        have := hyS (e.symm (SModel.codeIso.g g'))
        rw [hcode] at this
        rw [← this, Φ.g_f]
      have hsplit : (⟨(e.symm (b * SModel.codeIso.g g') : S), hST (e.symm _).2⟩ : T₁) =
          ⟨e.symm b, hST (e.symm b).2⟩ * ⟨e.symm (SModel.codeIso.g g'), hST (e.symm _).2⟩ := by
        apply Subtype.ext
        simp
      rw [hsplit, map_mul, hgen]
      calc c * (conjEquiv hyN ⟨e.symm b, hST (e.symm b).2⟩ * Φ.g ι[F g']!) =
          c * conjEquiv hyN ⟨e.symm b, hST (e.symm b).2⟩ * Φ.g ι[F g']! := (mul_assoc _ _ _).symm
        _ = conjEquiv hyN ⟨e.symm b, hST (e.symm b).2⟩ * (c * Φ.g ι[F g']!) := by
          rw [hb, mul_assoc]
        _ = conjEquiv hyN ⟨e.symm b, hST (e.symm b).2⟩ * Φ.g ι[F g']! * c := by
          rw [hc g' hg', mul_assoc]
  have hg' : g = conjEquiv hyN ⟨e.symm (e ⟨_, hg⟩), hST (e.symm (e ⟨_, hg⟩)).2⟩ := by
    apply Subtype.ext
    rw [conjEquiv_apply, MulEquiv.symm_apply_apply]
    change (g : G) = y * (y⁻¹ * g * y) * y⁻¹
    group
  rw [hg']
  exact key _

theorem comm_of_t1Gens {T₁ : Subgroup G} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso T₁ 131072 mul)
    (h0 : mul 0 0 = 0) (hG₁ : Gen mul t1Gens 131072) {c : T₁}
    (hc : ∀ g ∈ t1Gens, c * Φ.g g = Φ.g g * c) (g : T₁) : c * g = g * c := by
  refine Φ.induction h0 t1Gens_lt hG₁ (P := fun g => c * g = g * c) (by rw [mul_one, one_mul])
    ?_ g
  intro h hh g' hg'
  calc c * (h * Φ.g g') = c * h * Φ.g g' := (mul_assoc _ _ _).symm
    _ = h * (c * Φ.g g') := by rw [hh, mul_assoc]
    _ = h * Φ.g g' * c := by rw [hc g' hg', mul_assoc]

theorem mul_zero_right {T₁ : Subgroup G} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso T₁ 131072 mul)
    (h0 : mul 0 0 = 0) {a : ℕ} (ha : a < 131072) : mul a 0 = a := by
  have h := Φ.map_mul (Φ.g a) 1
  rw [mul_one, Φ.f_one h0, Φ.f_g ha] at h
  exact h.symm

theorem code_mul_cent {T₁ : Subgroup G} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso T₁ 131072 mul)
    (h0 : mul 0 0 = 0) {a : ℕ} (ha : a < 131072) {c : T₁} (hc : Φ.f c = 0 ∨ Φ.f c = 24) :
    Φ.f (Φ.g a * c) = a ∨ Φ.f (Φ.g a * c) = mul a 24 := by
  rw [Φ.map_mul, Φ.f_g ha]
  rcases hc with h | h
  · left
    rw [h, mul_zero_right Φ h0 ha]
  · right
    rw [h]

namespace Hyp

variable {ε : Eps} {t : G} {TH E₁ S : Subgroup G}

theorem false
    [Finite G] (hH : Hyp ε t TH E₁ S)
    (hGt : ∀ K : Subgroup G, K.index = 2 → t ∈ K) : False := by
  obtain ⟨e, he⟩ := hH.sylow.iso
  obtain ⟨x, hx, hxS, hx2, k, m, hk, hm, hmove, hd, hF, hT1⟩ := hH.level1 hGt he
  obtain ⟨j, hj, hkj, hmj, hzj⟩ := t1List_survivor hd rfl
  simp only at hkj hmj hzj
  subst hkj hmj
  have htS : t ∈ S := hH.t_mem_S
  have hF₁ : ∀ s : S, (sIso e).f ⟨x * s * x⁻¹, (mem_normalizer_iff.1 hx s).1 s.2⟩ =
      (fun c => (s2F j)[c]!) ((sIso e).f s) := by
    intro s
    rw [sIso_f, sIso_f]
    show _ = (sFTab (s2K j) (s2M j))[(e s).code]!
    rw [sFTab_get _ _ (e s).lt]
    exact hF s
  have hmul : ∀ a b, extMul 65536 sMul (fun c => (s2F j)[c]!) ((sIso e).f ⟨x * x, hx2⟩) a b =
      t1Mul (s2F j) (s2Z j) a b := by
    intro a b
    rw [sIso_f, hzj]
    rfl
  let Φ : CodeIso (S ⊔ zpowers x : Subgroup G) 131072 (t1Mul (s2F j) (s2Z j)) :=
    ((sIso e).extCodeIso hx hxS hx2 hF₁).copy (by norm_num) hmul
  have hST : S ≤ S ⊔ zpowers x := le_sup_left
  have hxT : x ∈ S ⊔ zpowers x := mem_sup_right (mem_zpowers x)
  have hΦS : ∀ (g : (S ⊔ zpowers x : Subgroup G)) (hg : (g : G) ∈ S),
      Φ.f g = (e ⟨g, hg⟩).code := by
    intro g hg
    show (sIso e).extF x g = _
    rw [CodeIso.extF_of_mem _ _ hg]
    rfl
  have hΦx : ∀ (g : (S ⊔ zpowers x : Subgroup G)), (g : G) ∉ S → ∀ hg : (g : G) * x⁻¹ ∈ S,
      Φ.f g = (e ⟨g * x⁻¹, hg⟩).code + 65536 := by
    intro g hg hg'
    show (sIso e).extF x g = _
    rw [CodeIso.extF_of_not_mem _ _ hg hg']
    rfl
  have hT : ∀ g : (S ⊔ zpowers x : Subgroup G), (g : G) ∈ S ∨ (g : G) * x⁻¹ ∈ S :=
    fun g => (mem_sup_zpowers_iff hx hx2).1 g.2
  have hS : ∀ g : (S ⊔ zpowers x : Subgroup G), (g : G) ∈ S ↔ Φ.f g < 65536 := by
    intro g
    constructor
    · intro hg; rw [hΦS g hg]; exact (e _).lt
    · intro hlt
      by_contra hg
      rw [hΦx g hg ((hT g).resolve_left hg)] at hlt
      omega
  have h0 : t1Mul (s2F j) (s2Z j) 0 0 = 0 := t1Mul_zero _ _
  have hG₁ : Gen (t1Mul (s2F j) (s2Z j)) t1Gens 131072 :=
    (sIso e).gen_ext sMul_zero_zero (fun c => (s2F j)[c]!) (s2Z j) sGens_lt sGen
  have hinv : ∀ c, c < 131072 → t1Inv (s2F j) (s2Z j) c < 131072 ∧
      t1Mul (s2F j) (s2Z j) c (t1Inv (s2F j) (s2Z j) c) = 0 := by
    have hkill := t1Kill_all hd
    simp only at hkill
    unfold t1Kill at hkill
    rw [hzj] at hkill
    exact fun c hc => inv_spec (groupKillC_spec hkill).1 hc
  have hT₁p : IsPGroup 2 (S ⊔ zpowers x : Subgroup G) :=
    isPGroup_sup_zpowers hH.sylow.pgroup hx hx2
  have hTHT₁ : TH ≤ S ⊔ zpowers x := hH.sylow.TH_le.trans le_sup_left
  have htT₁ : t ∈ S ⊔ zpowers x := mem_sup_left htS
  have hΦt : Φ.f ⟨t, htT₁⟩ = tCode ε := by
    rw [hΦS _ htS, ((he ⟨t, htS⟩).1).1 rfl, tM_code]
  have hTN : S ⊔ zpowers x ≤ normalizer (S : Set G) := sup_le le_normalizer (zpowers_le.2 hx)
  have hte : (e ⟨t, hH.t_mem_S⟩).code = tCode ε := by rw [((he ⟨t, htS⟩).1).1 rfl, tM_code]
  have hΦS' : ∀ (g : G) (hg : g ∈ S), Φ.f ⟨g, hST hg⟩ = (e ⟨g, hg⟩).code := fun g hg =>
    hΦS ⟨g, hST hg⟩ hg
  have hkill1 : t1Kill (s2K j) (s2M j) (s2Z j) Bool.false sMarked = true := by
    have hkill := t1Kill_all hd
    simp only at hkill
    rw [hzj] at hkill
    exact hkill
  have hmax := hH.maxN he hx hk hm hF hmove fpCount_eq
  obtain ⟨y, hyN, hyT, hy2⟩ := exists_step hT1
  have hyS : y ∉ normalizer (S : Set G) := by
    intro hyS
    apply hyT
    have hle : (S ⊔ zpowers x) ⊔ zpowers y ≤ normalizer (S : Set G) :=
      sup_le hTN (zpowers_le.2 hyS)
    have := hmax _ hle (isPGroup_sup_zpowers hT₁p hyN hy2) le_sup_left
    rw [← this]
    exact mem_sup_right (mem_zpowers y)
  obtain ⟨W, hW⟩ := l2eSurv_all hj
  unfold l2eSurvOK at hW
  simp only [Bool.and_eq_true] at hW
  obtain ⟨⟨⟨hvS, hchar⟩, hιOK⟩, henum⟩ := hW
  have hcard : Nat.card S = 65536 := by
    rw [Nat.card_congr e.toEquiv, SModel.codeIso.card_univ]
  have hSp : ∀ {y' : G}, y' ∈ normalizer ((S ⊔ zpowers x : Subgroup G) : Set G) →
      y' ∉ normalizer (S : Set G) → ∀ g : (S ⊔ zpowers x : Subgroup G),
        y'⁻¹ * g * y' ∈ S ↔ s2InSp (t1Vec W.vS) (Φ.f g) = true := by
    intro y' hy' hy'S
    have hv : (l2eTree W.vS).2.2.2 = t1Vec W.vS := by simp only [l2eTree]
    have h := sPrime_iff Φ h0 hS hST hcard (card_inv_S e) (card_ord4_S e) hy' hy'S
      (s2CharOK_of hvS hchar)
    simp only [hv] at h
    exact h
  have hkill1' : groupKillC (t1Mul (s2F j) (s2Z j)) (t1Inv (s2F j) (s2Z j)) t1Gens 131072 8
      Bool.false (chiB 10) (chiS 131072) sMarked (t1Cls (s2K j) (s2M j) (s2Z j)) = true := hkill1
  obtain ⟨hinvB, hcls, -, -⟩ := groupKillC_spec hkill1'
  have hι := iotaFacts_of Φ hinv hιOK
  obtain ⟨σ, k₂, hk₂, m₂, hm₂, hact₀⟩ := exists_twist e Φ h0 hι (hSp hyN hyS)
  obtain ⟨hy'N, hy'T, hy'2⟩ := step_mul (inv_mem σ.2) hyN hyT hy2
  have hy'S : (σ : G)⁻¹ * y ∉ normalizer (S : Set G) := fun h => hyS (by
    have : y = (σ : G) * ((σ : G)⁻¹ * y) := by group
    rw [this]; exact mul_mem (hTN σ.2) h)
  have hyS' : ∀ s : S, Φ.f (conjEquiv hy'N ⟨s, hST s.2⟩) =
      (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))[sFm k₂ m₂ (e s).code]! :=
    fun s => hact₀ s _
  have hF₁' : ∀ (s : S) (h : x * s * x⁻¹ ∈ S),
      (e ⟨x * s * x⁻¹, h⟩).code = (s2F j)[(e s).code]! := by
    intro s h
    show _ = (sFTab (s2K j) (s2M j))[(e s).code]!
    rw [sFTab_get _ _ (e s).lt]
    exact hF s
  have hB₁ := act_eq_s2B e Φ hST hxT hΦS hy'N hyS' hΦx hT
  have hv := mem_s2V Φ h0 hinv hy'N hy'2 hB₁
  have hSp' := hSp hy'N hy'S
  have hιlt : ∀ g ∈ sGens, (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))[g]! < 131072 :=
    fun g hg => hι.lt g (sGens_lt g hg)
  have hgι : ∀ g ∈ sGens, ((σ : G)⁻¹ * y)⁻¹ *
      (Φ.g (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))[g]! : G) *
        ((σ : G)⁻¹ * y) ∈ S := by
    intro g hg
    have h := conj_iotaF_mem Φ h0 hι hSp' (SModel.codeIso.g g)
    have hcode : (SModel.codeIso.g g).code = g := SModel.codeIso.f_g (sGens_lt g hg)
    unfold iotaF at h
    rwa [hcode] at h
  unfold l2eEnumOK at henum
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at henum
  obtain ⟨⟨hRs, hcent⟩, hleaf⟩ := henum
  have hl := hleaf k₂ hk₂ m₂ hm₂
  have hXconj : ∀ s₀, s₀ < 65536 → Φ.f (conjEquiv hy'N ⟨x, hxT⟩ *
      Φ.g (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))[sFm k₂ m₂ s₀]! *
        (conjEquiv hy'N ⟨x, hxT⟩)⁻¹) =
      (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))[sFm k₂ m₂ (s2F j)[s₀]!]! := by
    intro s₀ hs₀
    have hcode : (e (e.symm (SModel.codeIso.g s₀))).code = s₀ := by
      rw [MulEquiv.apply_symm_apply]
      exact SModel.codeIso.f_g hs₀
    have hxs : x * (e.symm (SModel.codeIso.g s₀) : G) * x⁻¹ ∈ S :=
      (mem_normalizer_iff.1 hx _).1 (e.symm (SModel.codeIso.g s₀)).2
    have h1 := hyS' (e.symm (SModel.codeIso.g s₀))
    rw [hcode] at h1
    have h2 := hyS' ⟨_, hxs⟩
    rw [hF₁' _ hxs, hcode] at h2
    rw [← h2, ← h1, Φ.g_f]
    refine congrArg Φ.f (Subtype.ext ?_)
    simp only [conjEquiv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hV : ∀ g : (S ⊔ zpowers x : Subgroup G),
      Φ.f ((⟨_, hy'2⟩ : (S ⊔ zpowers x : Subgroup G)) * g * (⟨_, hy'2⟩ : (S ⊔ zpowers x :
        Subgroup G))⁻¹) =
      s2B (t1Mul (s2F j) (s2Z j)) (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))
        (sFm k₂ m₂) (Φ.f (conjEquiv hy'N ⟨x, hxT⟩)) (s2B (t1Mul (s2F j) (s2Z j))
          (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j [])) (sFm k₂ m₂)
            (Φ.f (conjEquiv hy'N ⟨x, hxT⟩)) (Φ.f g)) := by
    intro g
    have e1 : (⟨_, hy'2⟩ : (S ⊔ zpowers x : Subgroup G)) * g *
        (⟨_, hy'2⟩ : (S ⊔ zpowers x : Subgroup G))⁻¹ = conjEquiv hy'N (conjEquiv hy'N g) := by
      apply Subtype.ext
      simp only [conjEquiv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1, hB₁ (conjEquiv hy'N g), hB₁ g]
  have act_kill : ∀ a, l2eActOK j k₂ m₂ (Φ.f (conjEquiv hy'N ⟨x, hxT⟩)) W.Rs a = true → False := by
    intro a ha
    unfold l2eActOK at ha
    dsimp only at ha
    rw [Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨haN, ha⟩ := ha
    split at ha
    ·
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
      obtain ⟨hx', hBx⟩ := ha
      rw [List.contains_iff_mem] at hx'
      have hz := l2eRec_conj Φ hinvB hG₁ hRs hx' haN ⟨_, hy'2⟩
      rw [hV, Φ.f_g haN] at hz
      exact Bool.false_ne_true (hBx.symm.trans (List.contains_iff_mem.2 hz))
    ·
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
        Bool.or_eq_true, List.contains_iff_mem] at ha
      obtain ⟨hv₀, hcase⟩ := ha
      have hsq : Φ.f ⟨_, hy'2⟩ = a.2.1 ∨ Φ.f ⟨_, hy'2⟩ = t1Mul (s2F j) (s2Z j) a.2.1 24 := by
        unfold s2V at hv
        simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq,
          List.all_eq_true] at hv
        obtain ⟨-, ⟨-, hvg⟩, -⟩ := hv
        have hcg : ∀ g ∈ t1Gens, ((Φ.g a.2.1)⁻¹ * ⟨_, hy'2⟩) * Φ.g g =
            Φ.g g * ((Φ.g a.2.1)⁻¹ * ⟨_, hy'2⟩) := by
          intro g hg
          obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.1 hg
          have hgD : t1Gens.getD i 0 = g := (List.getD_eq_getElem _ _ hi).trans hgi
          have hglt : g < 131072 := t1Gens_lt _ hg
          have hi10 : i < 10 := hi
          have e1 := hv₀ i hi10
          have e2 := hvg i hi10
          rw [getD_map_lt hi 0 0] at e2
          rw [hgD] at e1 e2
          rw [← e2] at e1
          have e3 := congrArg Φ.g e1
          rw [Φ.g_cconj h0 hinv haN hglt, Φ.g_cconj h0 hinv (Φ.lt _) hglt, Φ.g_f] at e3
          set Y : (S ⊔ zpowers x : Subgroup G) := ⟨_, hy'2⟩ with hY
          calc (Φ.g a.2.1)⁻¹ * Y * Φ.g g = (Φ.g a.2.1)⁻¹ * (Y * Φ.g g * Y⁻¹) * Y := by group
            _ = (Φ.g a.2.1)⁻¹ * (Φ.g a.2.1 * Φ.g g * (Φ.g a.2.1)⁻¹) * Y := by rw [e3]
            _ = Φ.g g * ((Φ.g a.2.1)⁻¹ * Y) := by group
        have hcen := comm_of_t1Gens Φ h0 hG₁ hcg
        have hc := cent_code Φ hinvB hG₁ hcent hSp' hιlt hgι (fun g _ => hcen g)
        have e4 : (⟨_, hy'2⟩ : (S ⊔ zpowers x : Subgroup G)) =
            Φ.g a.2.1 * ((Φ.g a.2.1)⁻¹ * ⟨_, hy'2⟩) := by group
        rw [e4]
        exact code_mul_cent Φ h0 haN hc
      rcases hcase with hcan | ⟨hR₀, hR₁⟩
      ·
        exact hH.false_of_canon hGt hj e hte hT₁p hST Φ hΦS' hG₁ hkill1 hι hcan hy'N hy'T hy'2
          hy'S hSp' hB₁ hsq
      ·
        obtain ⟨I, cents, recs, hsa⟩ := l2SurvAct_all hj
        unfold l2SurvActOK at hsa
        rw [Bool.and_eq_true] at hsa
        rcases hsq with hsq | hsq
        · obtain ⟨h16, hBχ, hvχ⟩ := l2eActR_spec Φ hinvB hG₁ hRs hcls hR₀
          exact hH.false_of_L2 hGt e hte hT₁p hST Φ hΦS' hG₁ hkill1 hι hy'N hy'T hy'2 hy'S hSp'
            hB₁ (l2TH_all ε) hsa.1 (l2K_all hj) h16 hBχ (by rw [hsq]; exact hvχ)
        · obtain ⟨h16, hBχ, hvχ⟩ := l2eActR_spec Φ hinvB hG₁ hRs hcls hR₁
          exact hH.false_of_L2 hGt e hte hT₁p hST Φ hΦS' hG₁ hkill1 hι hy'N hy'T hy'2 hy'S hSp'
            hB₁ (l2TH_all ε) hsa.1 (l2K_all hj) h16 hBχ (by rw [hsq]; exact hvχ)
  generalize W.LW.getD (32 * k₂ + m₂) (0, 0, 0, []) = lw at hl
  unfold l2eLeafOK at hl
  dsimp only at hl
  split at hl
  ·
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hl
    obtain ⟨⟨hs, hu⟩, hu'⟩ := hl
    rw [List.contains_iff_mem] at hu
    have hz := l2eRec_conj Φ hinvB hG₁ hRs hu (hι.lt _ (sF_lt _ _ _)) (conjEquiv hy'N ⟨x, hxT⟩)
    rw [hXconj _ hs] at hz
    exact Bool.false_ne_true (hu'.symm.trans (List.contains_iff_mem.2 hz))
  ·
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      beq_iff_eq] at hl
    obtain ⟨⟨hw₀, heq⟩, hacts⟩ := hl
    have hcomm : ∀ g ∈ sGens, (Φ.g lw.2.1)⁻¹ * conjEquiv hy'N ⟨x, hxT⟩ *
        Φ.g (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))[sFm k₂ m₂ g]! =
        Φ.g (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))[sFm k₂ m₂ g]! *
          ((Φ.g lw.2.1)⁻¹ * conjEquiv hy'N ⟨x, hxT⟩) := by
      intro g hg
      obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.1 hg
      have hgD : sGens.getD i 0 = g := (List.getD_eq_getElem _ _ hi).trans hgi
      have hi9 : i < 9 := hi
      have hg65 : g < 65536 := sGens_lt _ hg
      have he := heq i hi9
      rw [hgD] at he
      set ιt := s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []) with hιt
      set X : (S ⊔ zpowers x : Subgroup G) := conjEquiv hy'N ⟨x, hxT⟩ with hX
      have hU : ιt[sFm k₂ m₂ g]! < 131072 := hι.lt _ (sF_lt _ _ _)
      have hT' : ιt[sFm k₂ m₂ (s2F j)[g]!]! < 131072 := hι.lt _ (sF_lt _ _ _)
      have h1 : Φ.g lw.2.1 * Φ.g ιt[sFm k₂ m₂ g]! =
          Φ.g ιt[sFm k₂ m₂ (s2F j)[g]!]! * Φ.g lw.2.1 := by
        rw [← Φ.g_mul hw₀ hU, ← Φ.g_mul hT' hw₀, he]
      have h2 : X * Φ.g ιt[sFm k₂ m₂ g]! * X⁻¹ = Φ.g ιt[sFm k₂ m₂ (s2F j)[g]!]! := by
        rw [← hXconj _ hg65, Φ.g_f]
      calc (Φ.g lw.2.1)⁻¹ * X * Φ.g ιt[sFm k₂ m₂ g]! =
          (Φ.g lw.2.1)⁻¹ * (X * Φ.g ιt[sFm k₂ m₂ g]! * X⁻¹) * X := by group
        _ = (Φ.g lw.2.1)⁻¹ * (Φ.g lw.2.1 * Φ.g ιt[sFm k₂ m₂ g]! * (Φ.g lw.2.1)⁻¹) * X := by
          rw [h2, eq_mul_inv_of_mul_eq h1.symm]
        _ = Φ.g ιt[sFm k₂ m₂ g]! * ((Φ.g lw.2.1)⁻¹ * X) := by group
    have hcS := comm_of_gens e Φ hST hy'N hyS' hcomm
    have hc := cent_code Φ hinvB hG₁ hcent hSp' hιlt hgι hcS
    have hw : Φ.f (conjEquiv hy'N ⟨x, hxT⟩) = lw.2.1 ∨
        Φ.f (conjEquiv hy'N ⟨x, hxT⟩) = t1Mul (s2F j) (s2Z j) lw.2.1 24 := by
      have e1 : conjEquiv hy'N ⟨x, hxT⟩ =
          Φ.g lw.2.1 * ((Φ.g lw.2.1)⁻¹ * conjEquiv hy'N ⟨x, hxT⟩) := by group
      rw [e1]
      exact code_mul_cent Φ h0 hw₀ hc
    generalize lw.2.2.2 = acts at hacts
    rcases acts with _ | ⟨a₀, _ | ⟨a₁, _ | ⟨a₂, rest⟩⟩⟩
    · exact absurd hacts (by simp)
    · exact absurd hacts (by simp)
    · rw [Bool.and_eq_true] at hacts
      obtain ⟨ha₀, ha₁⟩ := hacts
      rcases hw with hw | hw
      · rw [← hw] at ha₀
        exact act_kill a₀ ha₀
      · rw [← hw] at ha₁
        exact act_kill a₁ ha₁
    · exact absurd hacts (by simp)

end Hyp

theorem not_index_two [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (K : Subgroup G) (hK : K.index = 2) : False := by
  have hN := Subgroup.normal_of_index_eq_two hK
  rcases hG.eq_bot_or_eq_top_of_normal K with h | h
  · rw [h, Subgroup.index_bot] at hK
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc : IsCyclic G := isCyclic_of_prime_card hK
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsCyclic.isMulCommutative (α := G)).is_comm.comm a b)
  · rw [h, Subgroup.index_top] at hK
    omega

theorem false_of_sylowModel
    [Finite G] {ε : Eps} {t : G} {TH E₁ S : Subgroup G}
    (ht : orderOf t = 2) (hTH : TH ≤ centralizer ({t} : Set G)) (hTHp : IsPGroup 2 TH)
    (hTHmax : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH)
    (hS : SylowModel ε t TH E₁ S) (hGt : ∀ K : Subgroup G, K.index = 2 → t ∈ K) : False := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  exact Hyp.false ⟨ht2, hTH, hTHp, hTHmax, hS⟩ hGt

theorem false_of_sylowModel_of_simple
    [Finite G]
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) {ε : Eps} {t : G}
    {TH E₁ S : Subgroup G} (ht : orderOf t = 2) (hTH : TH ≤ centralizer ({t} : Set G))
    (hTHp : IsPGroup 2 TH)
    (hTHmax : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH)
    (hS : SylowModel ε t TH E₁ S) : False :=
  false_of_sylowModel ht hTH hTHp hTHmax hS fun K hK => (not_index_two hG hnab K hK).elim

end CFSG.EvenSmallLie.OmegaEight.SpBranch
