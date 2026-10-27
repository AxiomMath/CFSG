module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Rank
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative Pointwise

namespace L1295C

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem psi_spec_F4 (h1222 : Stmt12_2_2_F4) (h : Hyp1281One G T L V n) (hn : n ≠ 3)
    (hV₁ : IsTSub T V V₁ 1) :
    ((actH (V₁ := V₁) (IH := V) inf_le_left inf_le_right).comp
        (Subgroup.inclusion (lOne_le h))).range = ⊤ ∧
      ((actH (V₁ := V₁) (IH := V) inf_le_left inf_le_right).comp
        (Subgroup.inclusion (lOne_le h))).ker = CFSG.pCore 2 ↥(lOne L V₁) := by
  set ψ := (actH (V₁ := V₁) (IH := V) inf_le_left inf_le_right).comp
    (Subgroup.inclusion (lOne_le (V₁ := V₁) h)) with hψ
  obtain ⟨Q, _, ρX, -, hker, htriv, -⟩ := exists_lOne_rep_F4 h1222 h hn hV₁

  have hkerle : ψ.ker ≤ CFSG.pCore 2 ↥(lOne L V₁) := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have hV : ∀ v ∈ V, (l : G) * v * (l : G)⁻¹ * v⁻¹ ∈ V₁ := by
      intro v hv
      have h1 := congrArg (fun f : MulAut ↥(tildeOf V₁ V) =>
        f (modMk (V_le_normalizer h hV₁) v hv)) hl
      simp only [MulAut.one_apply] at h1
      exact (actH_fix_iff h hV₁ _ hv).1 h1
    have h2 := htriv ⟨l, (oTwoUpper_le _) l.2⟩ hV
    rw [← hker]
    exact h2

  obtain ⟨e⟩ := lOne_quotient_mulEquiv_F4 h1222 h hn hV₁
  have hn1 : 1 ≤ n - 1 := by rcases h.n_mem with h | h | h <;> omega
  have hEA := isElemAbelian_tildeV (V₁ := V₁) h
  have : IsMulCommutative ↥(tildeOf V₁ V) := hEA.1
  have h1 := card_mulAut_le hEA.2 (card_tildeV h hV₁) hn1
  have h2 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := ZMod 2) hn1
  rw [Nat.card_zmod] at h2
  have hle1 : Nat.card (MulAut ↥(tildeOf V₁ V)) ≤
      Nat.card (↥(lOne L V₁) ⧸ CFSG.pCore 2 ↥(lOne L V₁)) := by
    rw [Nat.card_congr e.toEquiv, h2]
    exact h1
  have hle2 : Nat.card (↥(lOne L V₁) ⧸ CFSG.pCore 2 ↥(lOne L V₁)) ≤
      Nat.card (↥(lOne L V₁) ⧸ ψ.ker) := L1295A.card_quotient_le_of_le hkerle
  have hcardR : Nat.card (↥(lOne L V₁) ⧸ ψ.ker) = Nat.card ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  have hle3 : Nat.card ψ.range ≤ Nat.card (MulAut ↥(tildeOf V₁ V)) :=
    Subgroup.card_le_card_group _
  refine ⟨Subgroup.eq_top_of_le_card _ (hle1.trans (hle2.trans hcardR.le)), ?_⟩
  have heq : Nat.card (↥(lOne L V₁) ⧸ ψ.ker) =
      Nat.card (↥(lOne L V₁) ⧸ CFSG.pCore 2 ↥(lOne L V₁)) :=
    le_antisymm (hcardR.le.trans (hle3.trans hle1)) hle2
  have hc1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have hc2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(lOne L V₁))
  rw [heq] at hc1
  have hpos : 0 < Nat.card (↥(lOne L V₁) ⧸ CFSG.pCore 2 ↥(lOne L V₁)) := Nat.card_pos
  have hcardeq : Nat.card ψ.ker = Nat.card (CFSG.pCore 2 ↥(lOne L V₁)) :=
    Nat.eq_of_mul_eq_mul_left hpos (hc1.symm.trans hc2)
  exact Subgroup.eq_of_le_of_card_ge hkerle hcardeq.ge

theorem actH_eq_one_F4 (h1222 : Stmt12_2_2_F4) (h : Hyp1281One G T L V n) (hn : n ≠ 3)
    (hV₁ : IsTSub T V V₁ 1)
    (y : ↥(Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (V : Set G)))
    (hyL : (y : G) ∈ Subgroup.normalizer (lOne L V₁ : Set G))
    (hyc : ∀ l ∈ lOne L V₁, l * y * l⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 (lOne L V₁)) :
    actH (V₁ := V₁) (IH := V) inf_le_left inf_le_right y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hran, hker⟩ := psi_spec_F4 h1222 h hn hV₁
  set φ := actH (V₁ := V₁) (IH := V) inf_le_left inf_le_right with hφ

  have hcomm : ∀ τ : MulAut ↥(tildeOf V₁ V), φ y * τ = τ * φ y := by
    intro τ
    obtain ⟨l, hl⟩ : τ ∈ (φ.comp (Subgroup.inclusion (lOne_le h))).range := by
      rw [hran]
      exact Subgroup.mem_top τ
    rw [← hl]
    have hl' : (y : G) * l * (y : G)⁻¹ ∈ lOne L V₁ :=
      (Subgroup.mem_normalizer_iff.1 hyL _).1 l.2
    set l' : ↥(lOne L V₁) := ⟨_, hl'⟩ with hl'def
    have hll : l' * l⁻¹ ∈ CFSG.pCore 2 ↥(lOne L V₁) := by
      have h1 := Subgroup.inv_mem _ (hyc l l.2)
      have h2 : (((l' * l⁻¹ : ↥(lOne L V₁)) : G)) ∈ pCoreOf 2 (lOne L V₁) := by
        rw [show (((l' * l⁻¹ : ↥(lOne L V₁)) : G)) =
          ((l : G) * y * (l : G)⁻¹ * (y : G)⁻¹)⁻¹ by simp [hl'def]; group]
        exact h1
      obtain ⟨z, hz, hzl⟩ := h2
      have hzl' : z = l' * l⁻¹ := Subtype.ext hzl
      rw [← hzl', CFSG.pCore_eq_open, ← A3.pCore_eq_openCore]
      rw [A3.pCore_eq_openCore]
      exact hz
    have h3 : (φ.comp (Subgroup.inclusion (lOne_le h))) l' =
        (φ.comp (Subgroup.inclusion (lOne_le h))) l := by
      have h4 : l' * l⁻¹ ∈ (φ.comp (Subgroup.inclusion (lOne_le h))).ker := hker ▸ hll
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h4
      exact h4
    have h5 : (φ.comp (Subgroup.inclusion (lOne_le h))) l' =
        φ y * (φ.comp (Subgroup.inclusion (lOne_le h))) l * (φ y)⁻¹ := by
      simp only [MonoidHom.comp_apply, ← map_inv, ← map_mul]
      congr 1
    rw [h3] at h5
    calc φ y * (φ.comp (Subgroup.inclusion (lOne_le h))) l =
        (φ y * (φ.comp (Subgroup.inclusion (lOne_le h))) l * (φ y)⁻¹) * φ y := by group
      _ = (φ.comp (Subgroup.inclusion (lOne_le h))) l * φ y := by rw [← h5]

  have hEA := isElemAbelian_tildeV (V₁ := V₁) h
  let _ : CommGroup ↥(tildeOf V₁ V) := commGroupOfElemAbelian hEA
  have hW : ∀ w : ↥(tildeOf V₁ V), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hEA.2 w w.2)
  let _ : Module (ZMod 2) (Additive ↥(tildeOf V₁ V)) := Mult.zmodModuleW hW
  have : Module.Finite (ZMod 2) (Additive ↥(tildeOf V₁ V)) := Module.Finite.of_finite
  have hd : 2 ≤ Module.finrank (ZMod 2) (Additive ↥(tildeOf V₁ V)) := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥(tildeOf V₁ V))
    rw [Nat.card_zmod] at h1
    have h2 : Nat.card (Additive ↥(tildeOf V₁ V)) = 2 ^ (n - 1) := card_tildeV h hV₁
    rw [h2] at h1
    have h3 := (Nat.pow_right_injective le_rfl h1)
    have hn4 : 4 ≤ n := by rcases h.n_mem with h | h | h <;> omega
    omega
  set f := Mult.linEquiv (φ y) with hf
  have hfc : ∀ τ : Additive ↥(tildeOf V₁ V) ≃ₗ[ZMod 2] Additive ↥(tildeOf V₁ V),
      ∀ x, f (τ x) = τ (f x) := by
    intro τ x
    have h1 := congrArg Mult.linEquiv (hcomm (Mult.linEquiv.symm τ))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
    exact congrArg (fun g : Additive ↥(tildeOf V₁ V) ≃ₗ[ZMod 2] Additive ↥(tildeOf V₁ V) => g x) h1
  rcases Mult.eq_zero_or_eq_id_of_commute hd
      (φ := (f : Additive ↥(tildeOf V₁ V) →ₗ[ZMod 2] Additive ↥(tildeOf V₁ V))) hfc with h0 | hid
  · exfalso
    have : Nontrivial (Additive ↥(tildeOf V₁ V)) :=
      Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    obtain ⟨x, hx⟩ := exists_ne (0 : Additive ↥(tildeOf V₁ V))
    have h1 : f x = 0 := by
      have := congrArg (fun g : Additive ↥(tildeOf V₁ V) →ₗ[ZMod 2] Additive ↥(tildeOf V₁ V) =>
        g x) h0
      simpa using this
    exact hx (f.injective (h1.trans (map_zero f).symm))
  · apply Mult.linEquiv.injective
    rw [map_one]
    refine LinearEquiv.ext fun x => ?_
    have := congrArg (fun g : Additive ↥(tildeOf V₁ V) →ₗ[ZMod 2] Additive ↥(tildeOf V₁ V) =>
      g x) hid
    simpa using this

theorem mem_centralizer_F4 (h1222 : Stmt12_2_2_F4) (hcx : Cx1291 G T L V n) (hV₁ : IsTSub T V V₁ 1)
    {y : G} (hyM : y ∈ Subgroup.normalizer (L : Set G))
    (hyN₁ : y ∈ Subgroup.normalizer (V₁ : Set G)) (hy3 : y ^ 3 = 1)
    (hyc : ∀ l ∈ lOne L V₁, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 (lOne L V₁)) :
    y ∈ Subgroup.normalizer (V : Set G) ∧ y ∈ Subgroup.centralizer (V : Set G) := by
  have h := hcx.hyp
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  obtain ⟨-, hsq, hab⟩ := h.card_sq
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1

  have hyN : y ∈ Subgroup.normalizer (V : Set G) := by
    rcases h.hyp.ti_of_1222_F4 h1222 hyM with h1 | h1
    · exact SteinbergBS.mem_normalizer_of_conjugate_eq h1
    · exfalso
      have hle : V₁ ≤ V ⊓ CFSG.conjugate V y := le_inf hV₁.1 fun x hx => by
        rw [SteinbergBS.mem_conjugate_iff]
        exact hV₁.1 ((Subgroup.mem_normalizer_iff.1 hyN₁ x).1 hx)
      rw [h1, le_bot_iff] at hle
      rw [hle, Subgroup.card_bot] at hV₁2
      norm_num at hV₁2
  refine ⟨hyN, ?_⟩

  have hyL₁ : y ∈ Subgroup.normalizer (lOne L V₁ : Set G) :=
    normalizer_le_normalizer_oTwoUpper _
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hyM, Subgroup.le_normalizer hyN₁⟩)

  have h1 := actH_eq_one_F4 h1222 h hn hV₁ ⟨y, hyN₁, hyN⟩ hyL₁ hyc
  have hyV : ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ V₁ := fun v hv => by
    have := congrArg (fun f : MulAut ↥(tildeOf V₁ V) =>
      f (modMk (V_le_normalizer h hV₁) v hv)) h1
    simp only [MulAut.one_apply] at this
    exact (actH_fix_iff h hV₁ ⟨y, hyN₁, hyN⟩ hv).1 this

  have hyC₁ : y ∈ Subgroup.centralizer (V₁ : Set G) := by
    rw [← normalizer_eq_centralizer_of_card_eq_two hV₁2]
    exact hyN₁
  have hyy : y⁻¹ = y * y := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hy3)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨z, hzV₁, hzd⟩ : ∃ z, z ∈ V₁ ∧ z = y * v * y⁻¹ * v⁻¹ := ⟨_, hyV v hv, rfl⟩
  have hzy : z * y = y * z := Subgroup.mem_centralizer_iff.1 hyC₁ z hzV₁
  have hz2 : z * z = 1 := by
    have := hsq z (hV₁.1 hzV₁)
    rwa [sq] at this
  have hyv : y * v * y⁻¹ = z * v := by rw [hzd]; group
  have hyzy : y * z * y⁻¹ = z := by rw [← hzy]; group
  have h2 : y * (y * v * y⁻¹) * y⁻¹ = v := by
    rw [hyv]
    calc y * (z * v) * y⁻¹ = (y * z * y⁻¹) * (y * v * y⁻¹) := by group
      _ = z * (z * v) := by rw [hyv, hyzy]
      _ = v := by rw [← mul_assoc, hz2, one_mul]
  have h3 : y⁻¹ * v * y = v := by
    have e : y * (y * v * y⁻¹) * y⁻¹ = (y * y) * v * (y * y)⁻¹ := by group
    rw [e, ← hyy, inv_inv] at h2
    exact h2
  have h4 : y * v * y⁻¹ = v := by
    calc y * v * y⁻¹ = y * (y⁻¹ * v * y) * y⁻¹ := by rw [h3]
      _ = v := by group
  calc v * y = (y * v * y⁻¹) * y := by rw [h4]
    _ = y * v := by group

theorem false_of_order_three_F4 (h1222 : Stmt12_2_2_F4) (hcx : Cx1291 G T L V n)
    (hV₁ : IsTSub T V V₁ 1) {y : G} (hyM : y ∈ Subgroup.normalizer (L : Set G))
    (hyN₁ : y ∈ Subgroup.normalizer (V₁ : Set G)) (hy3 : orderOf y = 3)
    (hyc : ∀ l ∈ lOne L V₁, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 (lOne L V₁)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hcx.hyp
  have hyp := h.hyp
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  obtain ⟨hyN, hyC⟩ := mem_centralizer_F4 h1222 hcx hV₁ hyM hyN₁ hy3' hyc
  have hCL := inf_centralizer_eq_pCoreOf_F4 h1222 h
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1

  have hyl : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    intro l hl
    rw [← hCL]
    refine Subgroup.mem_inf.2
      ⟨L.mul_mem ((Subgroup.mem_normalizer_iff.1 hyM l).1 hl) (L.inv_mem hl), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hw : l⁻¹ * v * l ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (hLV (L.inv_mem hl)) v).1 hv
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hyC _ hw
    have h2 := Subgroup.mem_centralizer_iff.1 hyC v hv
    have h1' : (l⁻¹ * v * l) * y⁻¹ = y⁻¹ * (l⁻¹ * v * l) := by
      calc (l⁻¹ * v * l) * y⁻¹ = y⁻¹ * (y * (l⁻¹ * v * l)) * y⁻¹ := by group
        _ = y⁻¹ * ((l⁻¹ * v * l) * y) * y⁻¹ := by rw [h1]
        _ = y⁻¹ * (l⁻¹ * v * l) := by group
    calc v * (y * l * y⁻¹ * l⁻¹) = (v * y) * l * y⁻¹ * l⁻¹ := by group
      _ = (y * v) * l * y⁻¹ * l⁻¹ := by rw [h2]
      _ = y * l * ((l⁻¹ * v * l) * y⁻¹) * l⁻¹ := by group
      _ = y * l * (y⁻¹ * (l⁻¹ * v * l)) * l⁻¹ := by rw [h1']
      _ = y * l * y⁻¹ * l⁻¹ * v := by group

  have hyLC : ∀ w ∈ Subgroup.zpowers y, w ∈ L → w = 1 := by
    intro w hw hwL
    have hwC : w ∈ Subgroup.centralizer (V : Set G) := (Subgroup.zpowers_le.2 hyC) hw
    have hwO : w ∈ pCoreOf 2 L := hCL ▸ ⟨hwL, hwC⟩
    obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨w, hwO⟩
    have hk' : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    have hw3 : (y ^ m) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3', one_zpow]
    exact eq_one_of_two_pow_of_three hk' hw3

  set N := pCoreOf 2 L ⊔ Subgroup.zpowers y with hN
  set X := L ⊔ Subgroup.zpowers y with hX
  have hyO : Subgroup.zpowers y ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    Subgroup.zpowers_le.2 (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hyM)
  have hNX : N ≤ X := sup_le ((LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) le_sup_right
  have hL : ∀ g ∈ L, N ≤ N.comap (MulAut.conj g).toMonoidHom := by
    intro g hg
    refine sup_le (fun q hq => ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_left
        ((Subgroup.mem_normalizer_iff.1 (LieType.BorelTits.le_normalizer_pCoreOf 2 L hg) q).1 hq)
    · rw [Subgroup.mem_comap]
      show g * y * g⁻¹ ∈ N
      have h1 := hyl g⁻¹ (L.inv_mem hg)
      have h2 := (Subgroup.mem_normalizer_iff.1
        (LieType.BorelTits.le_normalizer_pCoreOf 2 L hg) _).1 h1
      rw [show g * y * g⁻¹ = (g * (y * g⁻¹ * y⁻¹ * g⁻¹⁻¹) * g⁻¹) * y by group]
      exact N.mul_mem (Subgroup.mem_sup_left h2) (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hY : ∀ g ∈ Subgroup.zpowers y, N ≤ N.comap (MulAut.conj g).toMonoidHom := by
    intro g hg
    refine sup_le (fun q hq => ?_) (fun w hw => ?_)
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hyO hg) q).1 hq)
    · rw [Subgroup.mem_comap]
      refine Subgroup.mem_sup_right ?_
      show g * w * g⁻¹ ∈ Subgroup.zpowers y
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hw) (Subgroup.inv_mem _ hg)
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := sup_le
    (fun g hg => mem_normalizer_of_comap (hL g hg) (hL g⁻¹ (L.inv_mem hg)))
    (fun g hg => mem_normalizer_of_comap (hY g hg) (hY g⁻¹ (Subgroup.inv_mem _ hg)))
  have hNn : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hXN

  have hL2 : 2 ≤ CFSG.Open.pRank 3 L := by
    have hP2 : IsPGroup 2 (CFSG.pCore 2 ↥L) := by
      rw [CFSG.pCore_eq_open]
      exact CFSG.LieType.BorelTits.pCore_isPGroup 2
    have hN3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
      obtain ⟨k, hk⟩ := hP2.exists_card_eq
      rw [hk]
      intro h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L,
      ← CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥L) hN3]
    obtain ⟨e⟩ := h.quot
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]
    rcases hcx.n45 with rfl | rfl
    · exact Rank8.two_le_pRank_sl_four
    · exact Rank8.two_le_pRank_sl_five
  obtain ⟨E₀, hE₀L, hE₀, hE₀card⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) L
  have hdvd : 3 ^ 2 ∣ Nat.card E₀ := by
    rw [hE₀card]
    exact pow_dvd_pow 3 hL2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  set E := K.map E₀.subtype with hE
  have hEE₀ : E ≤ E₀ := Subgroup.map_subtype_le K
  have hEab : IsElemAbelian 3 E := isElemAbelian_of_le hE₀ hEE₀
  have hEcard : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective E₀.subtype_injective, hK]
    norm_num
  have hEX : E ≤ X := (hEE₀.trans hE₀L).trans le_sup_left
  have hEN : E ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨heE, heN⟩
    have heL : e ∈ L := hE₀L (hEE₀ heE)
    have heN' : e ∈ ((pCoreOf 2 L : Set G) * (Subgroup.zpowers y : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hyO]
      exact heN
    obtain ⟨q, hq, w, hw, rfl⟩ := heN'
    have hwL : w ∈ L := by
      have := L.mul_mem (L.inv_mem ((LieType.BorelTits.pCoreOf_le 2 L) hq)) heL
      rwa [inv_mul_cancel_left] at this
    have hw1 := hyLC w hw hwL
    subst hw1
    have heE' : q ∈ E := by simpa using heE
    show q * 1 ∈ (⊥ : Subgroup G)
    rw [mul_one]
    obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨q, hq⟩
    have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subgroup.mem_bot.2 (eq_one_of_two_pow_of_three hk' (hEab.2 q heE'))
  have h3N : 3 ∣ Nat.card N := by
    have hyN' : y ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have := orderOf_dvd_natCard (⟨y, hyN'⟩ : ↥N)
    rwa [Subgroup.orderOf_mk, hy3] at this
  have h3X := S153D.three_le_pRank_of_acts hNX hNn hEX hEab hEcard hEN h3N

  have hXV : X ≤ Subgroup.normalizer (V : Set G) := sup_le hLV (Subgroup.zpowers_le.2 hyN)
  have hVT : V ≤ T := (hyp.le_and_normalizes_F4 h1222).1
  have hV2 : IsPGroup 2 V := hyp.sylow.1.to_le hVT
  have hVne : V ≠ ⊥ := by
    intro hb
    obtain ⟨hcard, -, -⟩ := h.card_sq
    rw [hb, Subgroup.card_bot] at hcard
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by rcases hcx.n45 with h | h <;> omega)
    omega
  have hO2 : pCoreOf 2 (Subgroup.normalizer (V : Set G)) ≠ ⊥ := by
    intro hb
    apply hVne
    rw [eq_bot_iff, ← hb]
    exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hV2
  have h2 := pRank_le_two_of_pCoreOf_ne_bot hyp.qtke hO2 Nat.prime_three (by norm_num)
  have h3 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hXV
  omega

end L1295C

end CFSG.Quasithin.H13
