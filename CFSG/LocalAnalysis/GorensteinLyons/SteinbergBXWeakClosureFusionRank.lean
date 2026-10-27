module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open scoped Pointwise
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

variable {D : Type*} [Group D]

theorem mem_conjugate_iff_wc {X : Subgroup D} {g x : D} :
    x ∈ CFSG.conjugate X g ↔ g * x * g⁻¹ ∈ X := by
  rw [CFSG.conjugate, mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem conjugate_conjugate_wc (X : Subgroup D) (a b : D) :
    CFSG.conjugate (CFSG.conjugate X a) b = CFSG.conjugate X (a * b) := by
  ext x
  rw [mem_conjugate_iff_wc, mem_conjugate_iff_wc, mem_conjugate_iff_wc]
  have : a * (b * x * b⁻¹) * a⁻¹ = a * b * x * (a * b)⁻¹ := by group
  rw [this]

theorem card_conjugate_wc (X : Subgroup D) (g : D) :
    Nat.card (CFSG.conjugate X g) = Nat.card X :=
  card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjugate_mono_wc {X Y : Subgroup D} (h : X ≤ Y) (g : D) :
    CFSG.conjugate X g ≤ CFSG.conjugate Y g :=
  map_mono h

theorem conjugate_inf_wc (X Y : Subgroup D) (g : D) :
    CFSG.conjugate (X ⊓ Y) g = CFSG.conjugate X g ⊓ CFSG.conjugate Y g := by
  ext x
  rw [mem_inf, mem_conjugate_iff_wc, mem_conjugate_iff_wc, mem_conjugate_iff_wc, mem_inf]

theorem conjugate_eq_self_iff_wc {X : Subgroup D} {g : D} :
    CFSG.conjugate X g = X ↔ g ∈ normalizer (X : Set D) := by
  rw [mem_normalizer_iff]
  constructor
  · intro h y
    conv_lhs => rw [← h]
    exact mem_conjugate_iff_wc
  · intro h
    ext x
    rw [mem_conjugate_iff_wc, ← h]

theorem mem_conjugate_of_mem_wc {X : Subgroup D} {x : D} (hx : x ∈ X) (g : D) :
    g⁻¹ * x * g ∈ CFSG.conjugate X g := by
  rw [mem_conjugate_iff_wc]
  simpa [mul_assoc] using hx

theorem exists_conjugate_le_of_isSylowOf [Finite D] {p : ℕ} [Fact p.Prime] {K R P : Subgroup D}
    (hR : IsSylowOf p R K) (hPK : P ≤ K) (hP : IsPGroup p P) :
    ∃ a ∈ K, CFSG.conjugate P a ≤ R := by
  have hP' : IsPGroup p (P.subgroupOf K) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  have hQK : IsSylowOf p ((Q : Subgroup K).map K.subtype) K := ⟨Q, rfl⟩
  obtain ⟨a, ha, hconj⟩ := hR.exists_mem_conj hQK
  refine ⟨a, ha, fun x hx => ?_⟩
  rw [mem_conjugate_iff_wc] at hx
  have h1 : a * x * a⁻¹ ∈ (Q : Subgroup K).map K.subtype :=
    ⟨⟨_, hPK hx⟩, hQ (mem_subgroupOf.mpr hx), rfl⟩
  have h2 := (hconj _).mp h1
  simpa [mul_assoc] using h2

theorem exists_isSylowOf_le [Finite D] {p : ℕ} [Fact p.Prime] {K P : Subgroup D} (hPK : P ≤ K)
    (hP : IsPGroup p P) : ∃ R, IsSylowOf p R K ∧ P ≤ R := by
  have hP' : IsPGroup p (P.subgroupOf K) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  exact ⟨_, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hPK hx⟩, hQ (mem_subgroupOf.mpr hx), rfl⟩⟩

theorem pRank_eq_of_elementary [Finite D] {p : ℕ} (hp : 1 < p) {X : Subgroup D}
    (hX : IsElemAbelian p X) {a : ℕ} (hXa : Nat.card X = p ^ a) : CFSG.pRank p X = a := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  have htop : IsElemAbelian p (⊤ : Subgroup X) :=
    ⟨⟨⟨fun u v => Subtype.ext (hX.1.is_comm.comm u.1 v.1)⟩⟩,
      fun x _ => Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hX.2 x x.2)⟩
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le hp fun F _ _ => ?_
    rw [← hXa]
    exact card_le_card_group F
  · refine CFSG.SectionRank.le_pRank hp le_rfl htop ?_
    rw [card_top, hXa]

theorem goldschmidt_weak_closure_fusion_rank_frontier [Finite D] (S : Sylow 2 D)
    {E : Subgroup D} (hES : E ≤ S) (hE : IsElemAbelian 2 E)
    (hwc : ∀ g : D, CFSG.conjugate E g ≤ S → CFSG.conjugate E g = E) :
    (E.subgroupOf S).Normal ∧
      ∀ [(E.subgroupOf S).Normal], ∀ t ∈ (S : Subgroup D), (∃ g : D, g⁻¹ * t * g ∈ E) →
        CFSG.pRank 2 (closure {x | ∃ e ∈ E, x = e⁻¹ * (t⁻¹ * e * t)}) ≤
          CFSG.pRank 2 (S ⧸ E.subgroupOf S) := by
  classical
  have := Fact.mk Nat.prime_two
  have : Fintype D := Fintype.ofFinite D
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE2 : ∀ a ∈ E, a * a = 1 := fun a ha => by rw [← pow_two]; exact hE.2 a ha
  have hEinv : ∀ a ∈ E, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (hE2 a ha)
  have hEp : ∀ {X : Subgroup D}, X ≤ E → IsPGroup 2 X := fun {X} hX x =>
    ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact hE.2 x (hX x.2))⟩
  have hSN : (S : Subgroup D) ≤ normalizer (E : Set D) := by
    intro s hs
    rw [← conjugate_eq_self_iff_wc]
    apply hwc
    intro x hx
    rw [mem_conjugate_iff_wc] at hx
    have : x = s⁻¹ * (s * x * s⁻¹) * s := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hs) (hES hx)) hs
  have hnorm : (E.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hES).mpr hSN
  refine ⟨hnorm, fun t ht ⟨g₀, hg₀⟩ => ?_⟩
  have hkey : ∀ (Q : Sylow 2 D) (c : D), CFSG.conjugate E c ≤ Q →
      (Q : Subgroup D) ≤ normalizer (CFSG.conjugate E c : Set D) := by
    intro Q c hcQ
    obtain ⟨y, hy⟩ := MulAction.exists_smul_eq D S Q
    have hQy : ∀ x, x ∈ (Q : Subgroup D) ↔ y⁻¹ * x * y ∈ (S : Subgroup D) := by
      intro x
      rw [← hy]
      change x ∈ MulAut.conj y • (S : Subgroup D) ↔ _
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
    have hcy : CFSG.conjugate E (c * y) = E := by
      apply hwc
      rw [← conjugate_conjugate_wc]
      intro x hx
      rw [mem_conjugate_iff_wc] at hx
      have h1 := (hQy _).mp (hcQ hx)
      simpa [mul_assoc] using h1
    intro q hq
    rw [← conjugate_eq_self_iff_wc]
    have hqS : y⁻¹ * q * y ∈ (S : Subgroup D) := (hQy q).mp hq
    have hE1 := (conjugate_eq_self_iff_wc (X := E)).mpr (hSN hqS)
    have e1 : CFSG.conjugate E c = CFSG.conjugate E y⁻¹ := by
      have h2 := congrArg (fun X => CFSG.conjugate X y⁻¹) hcy
      simp only [conjugate_conjugate_wc, mul_inv_cancel_right] at h2
      exact h2
    rw [e1, conjugate_conjugate_wc]
    calc CFSG.conjugate E (y⁻¹ * q) = CFSG.conjugate E ((y⁻¹ * q * y) * y⁻¹) := by group
      _ = CFSG.conjugate (CFSG.conjugate E (y⁻¹ * q * y)) y⁻¹ := (conjugate_conjugate_wc _ _ _).symm
      _ = CFSG.conjugate E y⁻¹ := by rw [hE1]
  have ht2 : t * t = 1 := by
    have h1 := hE2 _ hg₀
    have : t * t = g₀ * ((g₀⁻¹ * t * g₀) * (g₀⁻¹ * t * g₀)) * g₀⁻¹ := by group
    rw [this, h1, mul_one, mul_inv_cancel]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htE : ∀ e ∈ E, t⁻¹ * e * t ∈ E := fun e he => by
    simpa using (mem_normalizer_iff.mp (inv_mem (hSN ht)) e).mp he
  set Gt := Finset.univ.filter (fun g : D => g⁻¹ * t * g ∈ E) with hGt
  obtain ⟨g, hgGt, hgmax⟩ := Finset.exists_max_image Gt
    (fun g => Nat.card (E ⊓ CFSG.conjugate E g⁻¹ : Subgroup D))
    ⟨g₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg₀⟩⟩
  have hg : g⁻¹ * t * g ∈ E := (Finset.mem_filter.mp hgGt).2
  set E' := CFSG.conjugate E g⁻¹ with hE'def
  have hmemE' : ∀ x, x ∈ E' ↔ g⁻¹ * x * g ∈ E := fun x => by
    rw [hE'def, mem_conjugate_iff_wc, inv_inv]
  have htE' : t ∈ E' := (hmemE' t).mpr hg
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have h1 := hEcomm _ ((hmemE' a).mp ha) _ ((hmemE' b).mp hb)
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = b * a := by group
  set E₀ := E ⊓ E' with hE₀def
  have hE₀t : ∀ e ∈ E₀, e * t = t * e := fun e he => hE'comm e (mem_inf.mp he).2 t htE'
  set δ : D → D := fun e => e⁻¹ * (t⁻¹ * e * t) with hδdef
  have hδE : ∀ e ∈ E, δ e ∈ E := fun e he => mul_mem (inv_mem he) (htE e he)
  have hδmul : ∀ a ∈ E, ∀ b ∈ E, δ (a * b) = δ a * δ b := by
    intro a ha b hb
    have hc := hEcomm _ (htE a ha) _ (inv_mem hb)
    calc δ (a * b) = b⁻¹ * (a⁻¹ * (t⁻¹ * a * t)) * (t⁻¹ * b * t) := by simp only [hδdef]; group
      _ = b⁻¹ * a⁻¹ * ((t⁻¹ * a * t) * (t⁻¹ * b * t)) := by group
      _ = a⁻¹ * b⁻¹ * ((t⁻¹ * a * t) * (t⁻¹ * b * t)) := by
          rw [show b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ from by
            rw [← mul_inv_rev, ← mul_inv_rev, hEcomm a ha b hb]]
      _ = a⁻¹ * ((t⁻¹ * a * t) * b⁻¹) * (t⁻¹ * b * t) := by rw [hc]; group
      _ = δ a * δ b := by simp only [hδdef]; group
  have hδinv : ∀ a ∈ E, δ a⁻¹ = (δ a)⁻¹ := by
    intro a ha
    have h1 := hδmul a ha a⁻¹ (inv_mem ha)
    rw [mul_inv_cancel] at h1
    have h0 : δ 1 = 1 := by simp [hδdef]
    rw [h0] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hδt : ∀ e ∈ E, δ e * t = t * δ e := by
    intro e he
    have h1 : t * δ e * t = (δ e)⁻¹ := by
      have e1 : (δ e)⁻¹ = t⁻¹ * e⁻¹ * t * e := by simp only [hδdef]; group
      have e2 : t * δ e * t = t * e⁻¹ * t⁻¹ * e * (t * t) := by simp only [hδdef]; group
      rw [e1, e2, ht2, mul_one, htinv]
    have h2 : (δ e)⁻¹ = δ e := hEinv _ (hδE e he)
    have h3 : t * (t * δ e * t) = δ e * t := by
      rw [← mul_assoc, ← mul_assoc, ht2, one_mul]
    rw [← h3, h1, h2]
  set C := E ⊓ centralizer ({t} : Set D) with hCdef
  have hmemC : ∀ e, e ∈ C ↔ e ∈ E ∧ e * t = t * e := fun e => by
    rw [hCdef, mem_inf, mem_centralizer_singleton_iff]
  have hδC : ∀ e ∈ E, δ e = 1 ↔ e * t = t * e := by
    intro e he
    simp only [hδdef]
    constructor
    · intro h
      have : t⁻¹ * e * t = e := by
        have := congrArg (e * ·) h
        simpa [mul_assoc] using this
      calc e * t = t * (t⁻¹ * e * t) := by group
        _ = t * e := by rw [this]
    · intro h
      have : t⁻¹ * e * t = e := by rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [this, inv_mul_cancel]
  let E₂ : Subgroup D :=
    { carrier := {e | e ∈ E ∧ δ e ∈ E₀}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [hδmul a ha.1 b hb.1]
        exact mul_mem ha.2 hb.2⟩
      one_mem' := ⟨one_mem _, by simp [hδdef]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        rw [hδinv a ha.1]
        exact inv_mem ha.2⟩ }
  have hmemE₂ : ∀ e, e ∈ E₂ ↔ e ∈ E ∧ δ e ∈ E₀ := fun _ => Iff.rfl
  have hE₂E : E₂ ≤ E := fun e he => he.1
  have hCE₂ : C ≤ E₂ := fun e he => by
    obtain ⟨heE, het⟩ := (hmemC e).mp he
    refine ⟨heE, ?_⟩
    rw [(hδC e heE).mpr het]
    exact one_mem _
  have hE₀C : E₀ ≤ C := fun e he => (hmemC e).mpr ⟨(mem_inf.mp he).1, hE₀t e he⟩
  have hE₀E₂ : E₀ ≤ E₂ := hE₀C.trans hCE₂
  set E₁ := E₀ ⊔ zpowers t with hE₁def
  have hE₁E' : E₁ ≤ E' := sup_le (fun e he => (mem_inf.mp he).2) (zpowers_le.mpr htE')
  have hE'N : E' ≤ normalizer (E₁ : Set D) := by
    intro y hy
    apply mem_normalizer_fintype
    intro x hx
    have hxy := hE'comm y hy x (hE₁E' hx)
    rw [hxy, mul_inv_cancel_right]
    exact hx
  have hE₂N : E₂ ≤ normalizer (E₁ : Set D) := by
    intro e he
    apply mem_normalizer_fintype
    have hle : E₁ ≤ E₁.comap (MulAut.conj e).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (zpowers_le.mpr ?_)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          hEcomm e he.1 x (mem_inf.mp hx).1, mul_inv_cancel_right]
        exact mem_sup_left hx
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have hc := hEcomm _ (htE e he.1) _ (inv_mem he.1)
        have : e * t * e⁻¹ = t * δ e := by
          simp only [hδdef]
          rw [← hc]
          group
        rw [this]
        exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left he.2)
    intro x hx
    have := hle hx
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hE'p : IsPGroup 2 E' := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    have h1 := hE.2 _ ((hmemE' x).mp x.2)
    have h2 : g⁻¹ * ((x : D) ^ 2) * g = 1 := by
      rw [← h1, pow_two, pow_two]
      group
    have : (x : D) ^ 2 = g * (g⁻¹ * ((x : D) ^ 2) * g) * g⁻¹ := by group
    rw [this, h2, mul_one, mul_inv_cancel]
  obtain ⟨R, hR, hE'R⟩ := exists_isSylowOf_le hE'N hE'p
  obtain ⟨Q, hRQ⟩ := hR.isPGroup.exists_le_sylow
  have hQN : (Q : Subgroup D) ≤ normalizer (E' : Set D) := hkey Q g⁻¹ (hE'R.trans hRQ)
  obtain ⟨a, ha, haR⟩ := exists_conjugate_le_of_isSylowOf hR hE₂N (hEp hE₂E)
  have hP₂ : CFSG.conjugate E₂ (a * g) ≤ normalizer (E : Set D) := by
    intro x hx
    rw [← conjugate_conjugate_wc] at hx
    rw [← conjugate_eq_self_iff_wc]
    rw [mem_conjugate_iff_wc] at hx
    have h1 := hQN (hRQ (haR hx))
    rw [← conjugate_eq_self_iff_wc] at h1
    have h2 : CFSG.conjugate E' g = E := by
      rw [hE'def, conjugate_conjugate_wc, inv_mul_cancel]
      ext y
      rw [mem_conjugate_iff_wc]
      simp
    calc CFSG.conjugate E x = CFSG.conjugate (CFSG.conjugate E' g) x := by rw [h2]
      _ = CFSG.conjugate E' (g * x) := conjugate_conjugate_wc _ _ _
      _ = CFSG.conjugate E' ((g * x * g⁻¹) * g) := by group
      _ = CFSG.conjugate (CFSG.conjugate E' (g * x * g⁻¹)) g :=
          (conjugate_conjugate_wc _ _ _).symm
      _ = E := by rw [h1, h2]
  have hSsyl : IsSylowOf 2 (S : Subgroup D) (normalizer (E : Set D)) := by
    rw [isSylowOf_iff]
    refine ⟨hSN, S.isPGroup', fun hdvd => ?_⟩
    apply S.not_dvd_index
    rw [← relIndex_mul_index hSN]
    exact hdvd.mul_right _
  obtain ⟨n, hn, hnS⟩ := exists_conjugate_le_of_isSylowOf hSsyl hP₂
    ((hEp hE₂E).map (MulAut.conj (a * g)⁻¹).toMonoidHom)
  set h := a * g * n with hhdef
  have hE₂hS : CFSG.conjugate E₂ h ≤ S := by
    rw [hhdef, ← conjugate_conjugate_wc]
    exact hnS
  have hE₁h : CFSG.conjugate E₁ h ≤ E := by
    have h1 : CFSG.conjugate E₁ a = E₁ := conjugate_eq_self_iff_wc.mpr ha
    have h2 : CFSG.conjugate E₁ g ≤ E := by
      intro x hx
      rw [mem_conjugate_iff_wc] at hx
      have h3 := (hmemE' _).mp (hE₁E' hx)
      simpa [mul_assoc] using h3
    have h3 : CFSG.conjugate E n = E := conjugate_eq_self_iff_wc.mpr hn
    rw [hhdef, ← conjugate_conjugate_wc, ← conjugate_conjugate_wc, h1]
    calc CFSG.conjugate (CFSG.conjugate E₁ g) n ≤ CFSG.conjugate E n := conjugate_mono_wc h2 n
      _ = E := h3
  have hth : h⁻¹ * t * h ∈ E := hE₁h (mem_conjugate_of_mem_wc (mem_sup_right (mem_zpowers t)) h)
  have hmax := hgmax h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hth⟩)
  have hcardh : Nat.card (E ⊓ CFSG.conjugate E h : Subgroup D) =
      Nat.card (E ⊓ CFSG.conjugate E h⁻¹ : Subgroup D) := by
    have e1 : CFSG.conjugate (E ⊓ CFSG.conjugate E h⁻¹) h = CFSG.conjugate E h ⊓ E := by
      rw [conjugate_inf_wc, conjugate_conjugate_wc, inv_mul_cancel]
      congr 1
      ext y
      rw [mem_conjugate_iff_wc]
      simp
    rw [inf_comm, ← e1, card_conjugate_wc]
  have hE₀h : CFSG.conjugate E₀ h ≤ E ⊓ CFSG.conjugate E h :=
    le_inf ((conjugate_mono_wc le_sup_left h).trans hE₁h) (conjugate_mono_wc inf_le_left h)
  have hEEh : E ⊓ CFSG.conjugate E h = CFSG.conjugate E₀ h := by
    refine (eq_of_le_of_card_ge hE₀h ?_).symm
    rw [card_conjugate_wc, hcardh]
    exact hmax
  have hEE₂h : E ⊓ CFSG.conjugate E₂ h = CFSG.conjugate E₀ h := by
    apply le_antisymm
    · rw [← hEEh]
      exact inf_le_inf_left E (conjugate_mono_wc hE₂E h)
    · exact le_inf (hE₀h.trans inf_le_left) (conjugate_mono_wc hE₀E₂ h)
  set ψ : E₂ →* S ⧸ E.subgroupOf S :=
    (QuotientGroup.mk' (E.subgroupOf S)).comp
      (((MulAut.conj h⁻¹).toMonoidHom.comp E₂.subtype).codRestrict S fun e =>
        hE₂hS (by
          change h⁻¹ * (e : D) * h⁻¹⁻¹ ∈ CFSG.conjugate E₂ h
          rw [inv_inv]
          exact mem_conjugate_of_mem_wc e.2 h)) with hψdef
  have hψker : ψ.ker = E₀.subgroupOf E₂ := by
    ext e
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change QuotientGroup.mk' (E.subgroupOf S) _ = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    change h⁻¹ * (e : D) * h⁻¹⁻¹ ∈ E ↔ _
    rw [inv_inv]
    constructor
    · intro he
      have h1 : h⁻¹ * (e : D) * h ∈ E ⊓ CFSG.conjugate E₂ h :=
        mem_inf.mpr ⟨he, mem_conjugate_of_mem_wc e.2 h⟩
      rw [hEE₂h, mem_conjugate_iff_wc] at h1
      simpa [mul_assoc] using h1
    · intro he
      have h1 := mem_conjugate_of_mem_wc he h
      rw [← hEE₂h] at h1
      exact (mem_inf.mp h1).1
  have hψel : IsElemAbelian 2 ψ.range := by
    refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨x', hx'⟩ := u.2
      obtain ⟨y', hy'⟩ := v.2
      change (u : S ⧸ E.subgroupOf S) * v = v * u
      rw [← hx', ← hy', ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEcomm _ (hE₂E x'.2) _ (hE₂E y'.2))
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hE.2 _ (hE₂E x.2))
      rw [this, map_one]
  have hψcard : Nat.card ψ.range * Nat.card E₀ = Nat.card E₂ := by
    have h1 := card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hψker,
      Nat.card_congr (subgroupOfEquivOfLe hE₀E₂).toEquiv] at h1
    exact h1.symm
  set Rt := closure {x | ∃ e ∈ E, x = e⁻¹ * (t⁻¹ * e * t)} with hRtdef
  let δh : E →* D :=
    { toFun := fun e => δ e
      map_one' := by simp [hδdef]
      map_mul' := fun a b => hδmul a a.2 b b.2 }
  have hRt : Rt = δh.range := by
    apply le_antisymm
    · rw [hRtdef, closure_le]
      rintro _ ⟨e, he, rfl⟩
      exact ⟨⟨e, he⟩, rfl⟩
    · rintro _ ⟨e, rfl⟩
      exact subset_closure ⟨e, e.2, rfl⟩
  have hRtE : Rt ≤ E := by
    rw [hRt]
    rintro _ ⟨e, rfl⟩
    exact hδE e e.2
  have hRtC : Rt ≤ C := by
    rw [hRt]
    rintro _ ⟨e, rfl⟩
    exact (hmemC _).mpr ⟨hδE e e.2, hδt e e.2⟩
  have hkerδ : ∀ e : E, e ∈ δh.ker ↔ (e : D) ∈ C := fun e => by
    rw [MonoidHom.mem_ker, hmemC]
    exact ⟨fun h1 => ⟨e.2, (hδC e e.2).mp h1⟩, fun h1 => (hδC e e.2).mpr h1.2⟩
  have hcardE : Nat.card E = Nat.card Rt * Nat.card C := by
    have h1 := card_eq_card_quotient_mul_card_subgroup δh.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange δh).toEquiv, ← hRt] at h1
    rw [h1]
    congr 1
    have hk : δh.ker = C.subgroupOf E := by
      ext e
      rw [hkerδ, mem_subgroupOf]
    rw [hk]
    exact Nat.card_congr (subgroupOfEquivOfLe (hCE₂.trans hE₂E)).toEquiv
  let δ₂ : E₂ →* D := δh.comp (inclusion hE₂E)
  have hδ₂range : δ₂.range = Rt ⊓ E₀ := by
    apply le_antisymm
    · rintro _ ⟨e, rfl⟩
      refine mem_inf.mpr ⟨?_, e.2.2⟩
      rw [hRt]
      exact ⟨inclusion hE₂E e, rfl⟩
    · intro x hx
      obtain ⟨hxR, hxE₀⟩ := mem_inf.mp hx
      rw [hRt] at hxR
      obtain ⟨e, rfl⟩ := hxR
      exact ⟨⟨e, e.2, hxE₀⟩, rfl⟩
  have hcardE₂ : Nat.card E₂ = Nat.card (Rt ⊓ E₀ : Subgroup D) * Nat.card C := by
    have h1 := card_eq_card_quotient_mul_card_subgroup δ₂.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange δ₂).toEquiv, hδ₂range] at h1
    rw [h1]
    congr 1
    have hk : δ₂.ker = C.subgroupOf E₂ := by
      ext e
      rw [mem_subgroupOf]
      exact hkerδ (inclusion hE₂E e)
    rw [hk]
    exact Nat.card_congr (subgroupOfEquivOfLe hCE₂).toEquiv
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Rt E₀ fun x hx y hy =>
    hEcomm x (hRtE hx) y ((mem_inf.mp hy).1)).1
  have hsupC : Nat.card (Rt ⊔ E₀ : Subgroup D) ≤ Nat.card C :=
    card_le_of_le (sup_le hRtC hE₀C)
  have hcount : Nat.card Rt * Nat.card E₀ ≤ Nat.card E₂ := by
    rw [← hprod, hcardE₂, mul_comm (Nat.card (Rt ⊓ E₀ : Subgroup D))]
    exact Nat.mul_le_mul_right _ hsupC
  have hRtψ : Nat.card Rt ≤ Nat.card ψ.range := by
    have hE₀pos : 0 < Nat.card E₀ := Nat.card_pos
    rw [← hψcard] at hcount
    exact Nat.le_of_mul_le_mul_right hcount hE₀pos
  have hRtel : IsElemAbelian 2 Rt :=
    ⟨⟨⟨fun u v => Subtype.ext (hEcomm _ (hRtE u.2) _ (hRtE v.2))⟩⟩,
      fun x hx => hE.2 x (hRtE hx)⟩
  obtain ⟨aR, haR⟩ := (IsPGroup.iff_card (p := 2)).mp (hEp hRtE)
  have hψp : IsPGroup 2 ψ.range := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hψel.2 x x.2)⟩
  obtain ⟨bR, hbR⟩ := (IsPGroup.iff_card (p := 2)).mp hψp
  have h1 : CFSG.pRank 2 Rt = aR := pRank_eq_of_elementary (by norm_num) hRtel haR
  have h2 : bR ≤ CFSG.pRank 2 (S ⧸ E.subgroupOf S) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top hψel hbR
  have h3 : aR ≤ bR := by
    rw [haR, hbR] at hRtψ
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hRtψ
  rw [h1]
  exact h3.trans h2

end CFSG.LocalAnalysis.GorensteinLyons
