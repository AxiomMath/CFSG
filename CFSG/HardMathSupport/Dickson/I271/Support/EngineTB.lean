module

public import CFSG.HardMathSupport.Dickson.I271.Support.EngineQ
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineBasic
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem glaPLayer_top_eq_bot_of_coprime_quotient {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) {N M : Subgroup Y} [N.Normal] (hNp : IsPGroup p N) (hNM : N ≤ M)
    (hexp : ∀ x ∈ M, ∃ n : ℕ, Nat.Coprime p n ∧ x ^ n ∈ N) (hab : commutator Y ≤ M) :
    GLAPLayer p (⊤ : Subgroup Y) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold GLAPLayer
  refine eq_bot_iff.2 (sSup_le fun L hL => ?_)
  exfalso
  obtain ⟨-, -, hcomp, -⟩ := hL
  set Z := ↥(⊤ : Subgroup Y) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup Y) with hZ
  set φ : Y →* Z :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup Y))).comp
      (Subgroup.topEquiv.symm : Y ≃* ↥(⊤ : Subgroup Y)).toMonoidHom with hφ
  have hφs : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp (MulEquiv.surjective _)
  haveI : (N.map φ).Normal := Subgroup.Normal.map ‹N.Normal› φ hφs
  have hO : GLAPPrimeCore p Z = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hexpZ : ∀ x ∈ M.map φ, ∃ n : ℕ, Nat.Coprime p n ∧ x ^ n ∈ N.map φ := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨n, hn, hmn⟩ := hexp m hm
    exact ⟨n, hn, ⟨m ^ n, hmn, by rw [map_pow]⟩⟩
  have habZ : commutator Z ≤ M.map φ := by
    have : commutator Z = (commutator Y).map φ := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective φ hφs]
    rw [this]
    exact Subgroup.map_mono hab
  have hle := le_of_isComponentOf_of_coprime_quotient hp hO (Subgroup.map_mono hNM) hexpZ habZ hcomp
  have hpg : IsPGroup p ↥((L.subgroupOf (⊤ : Subgroup Y)).map
      (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup Y)))) :=
    (hNp.map φ).to_le hle
  set K' : Subgroup Z := (L.subgroupOf (⊤ : Subgroup Y)).map
      (QuotientGroup.mk' (GLAPPrimeCore p ↥(⊤ : Subgroup Y))) with hK'
  haveI : Group.IsNilpotent ↥K' := hpg.isNilpotent
  have hq : CFSG.Open.IsQuasisimple ↥K' := hcomp.2.2
  haveI : Group.IsPerfect ↥K' := ⟨hq.1⟩
  haveI := CFSG.ComponentClassification.Quasisimple.nontrivial hq
  exact Group.IsPerfect.not_isSolvable _ (inferInstance : Group.IsSolvable ↥K')

theorem centralizes_pCore_of_isSCp_coprime (i20 : Input20_1) {Q : Type} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B W : Subgroup Q} (hB : IsSCp p ⊤ B)
    (hW : Nat.Coprime p (Nat.card W)) (hBW : B ≤ Subgroup.normalizer (W : Set Q)) :
    W ≤ Subgroup.centralizer (CFSG.Open.pCore p Q : Set Q) := by
  have : Fact p.Prime := ⟨hp⟩
  have hPn : (CFSG.Open.pCore p Q).Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hPp : IsPGroup p (CFSG.Open.pCore p Q) := CFSG.LieType.BorelTits.pCore_isPGroup (G := Q) p
  set P := CFSG.Open.pCore p Q with hP
  set Y := P ⊔ (W ⊔ B) with hY
  have hPY : P ≤ Y := le_sup_left
  have hWY : W ≤ Y := le_sup_left.trans le_sup_right
  have hBY : B ≤ Y := le_sup_right.trans le_sup_right
  have hPW : P ⊔ W ≤ Y := sup_le hPY hWY
  have hWPn : W ≤ Subgroup.normalizer (P : Set Q) := (Subgroup.normalizer_eq_top_iff.2 hPn) ▸ le_top
  have hlayer : GLAPLayer p (⊤ : Subgroup ↥Y) = ⊥ := by
    haveI : (P.subgroupOf Y).Normal := inferInstance
    have hNp : IsPGroup p ↥(P.subgroupOf Y) :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm
    have hNM : P.subgroupOf Y ≤ (P ⊔ W).subgroupOf Y := fun x hx =>
      (Subgroup.mem_subgroupOf).2 ((le_sup_left : P ≤ P ⊔ W) ((Subgroup.mem_subgroupOf).1 hx))
    have hexp : ∀ x ∈ (P ⊔ W).subgroupOf Y, ∃ n : ℕ, Nat.Coprime p n ∧
        x ^ n ∈ P.subgroupOf Y := by
      intro x hx
      refine ⟨Nat.card W, hW, ?_⟩
      have := pow_mem_of_mem_sup (K := P) (W := W) hWPn ((Subgroup.mem_subgroupOf).1 hx)
      exact (Subgroup.mem_subgroupOf).2 (by simpa using this)
    have hBPW : B ≤ Subgroup.normalizer ((P ⊔ W : Subgroup Q) : Set Q) := fun b hb =>
      mem_normalizer_sup ((Subgroup.normalizer_eq_top_iff.2 hPn) ▸ Subgroup.mem_top b) (hBW hb)
    have hYN : Y ≤ Subgroup.normalizer ((P ⊔ W : Subgroup Q) : Set Q) := by
      have : Y = (P ⊔ W) ⊔ B := by rw [hY, sup_assoc]
      rw [this]
      exact sup_le Subgroup.le_normalizer hBPW
    haveI hMn : ((P ⊔ W).subgroupOf Y).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPW).2 hYN
    have hMB : (P ⊔ W).subgroupOf Y ⊔ B.subgroupOf Y = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hPW hBY]
      have : P ⊔ W ⊔ B = Y := by rw [hY, sup_assoc]
      rw [this]
      exact Subgroup.subgroupOf_self Y
    have hab : commutator ↥Y ≤ (P ⊔ W).subgroupOf Y := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      exact commutator_mem_of_sup_eq_top hMB
        (fun a ha b hb => Subtype.ext (CFSG.Open.IsElemAbelian.comm hB.2.1
          ((Subgroup.mem_subgroupOf).1 ha) ((Subgroup.mem_subgroupOf).1 hb))) x y
    exact glaPLayer_top_eq_bot_of_coprime_quotient hp hNp hNM hexp hab
  have hB' : IsSCp p ⊤ (B.subgroupOf Y) := isSCp_subgroupOf hB hBY
  have hmain := i20 ↥Y p hp hp2 hlayer (B.subgroupOf Y) hB'
  have hWcop : Nat.Coprime p (Nat.card (W.subgroupOf Y)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWY).toEquiv]
    exact hW
  have hWnorm : B.subgroupOf Y ≤
      Subgroup.normalizer ((W.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := Subgroup.mem_normalizer_iff.1 (hBW ((Subgroup.mem_subgroupOf).1 hb)) (x : Q)
    simpa [Subgroup.mem_subgroupOf] using this
  have hWO : W.subgroupOf Y ≤ GLAPPrimeCoreOf p (⊤ : Subgroup ↥Y) :=
    hmain ▸ le_iSup_of_le (W.subgroupOf Y) (le_iSup_of_le hWcop (le_iSup_of_le hWnorm le_rfl))
  have hOn := le_normalizer_glaPPrimeCoreOf p (⊤ : Subgroup ↥Y)
  have hOcop := not_dvd_card_glaPPrimeCoreOf hp (⊤ : Subgroup ↥Y)
  intro x hx q hq
  set xY : ↥Y := ⟨x, hWY hx⟩
  set qY : ↥Y := ⟨q, hPY hq⟩
  have hxO : xY ∈ GLAPPrimeCoreOf p (⊤ : Subgroup ↥Y) := hWO ((Subgroup.mem_subgroupOf).2 hx)
  have hc1 : xY * (qY * xY⁻¹ * qY⁻¹) ∈ GLAPPrimeCoreOf p (⊤ : Subgroup ↥Y) := by
    refine Subgroup.mul_mem _ hxO ?_
    have := (Subgroup.mem_normalizer_iff.1 (hOn (Subgroup.mem_top qY)) xY⁻¹).1
      (Subgroup.inv_mem _ hxO)
    simpa using this
  have hc2 : (xY * (qY * xY⁻¹ * qY⁻¹) : ↥Y) ∈ P.subgroupOf Y := by
    rw [Subgroup.mem_subgroupOf]
    have h1 : x * q * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normalizer_eq_top_iff.2 hPn) ▸ Subgroup.mem_top x) q).1 hq
    have : ((xY * (qY * xY⁻¹ * qY⁻¹) : ↥Y) : Q) = (x * q * x⁻¹) * q⁻¹ := by
      simp [xY, qY, mul_assoc]
    rw [this]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hq)
  set c : ↥Y := xY * (qY * xY⁻¹ * qY⁻¹) with hc
  have hcard := Subgroup.orderOf_dvd_natCard (GLAPPrimeCoreOf p (⊤ : Subgroup ↥Y)) hc1
  obtain ⟨n, hn⟩ := hPp ⟨(c : Q), (Subgroup.mem_subgroupOf).1 hc2⟩
  have hn' : c ^ (p ^ n) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
  have hcop : Nat.Coprime p (orderOf c) :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hOcop).coprime_dvd_right hcard
  have h1 : orderOf c = 1 :=
    (Nat.Coprime.pow_left n hcop).symm.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hn')
  have hc1' : c = 1 := orderOf_eq_one_iff.1 h1
  have : (x * q * x⁻¹ * q⁻¹ : Q) = 1 := by
    have := congrArg Subtype.val hc1'
    simpa [c, xY, qY, mul_assoc] using this
  calc q * x = (x * q * x⁻¹ * q⁻¹) * (q * x) := by rw [this, one_mul]
    _ = x * q := by group

end CFSG.HardMathSupport.Dickson.I271
