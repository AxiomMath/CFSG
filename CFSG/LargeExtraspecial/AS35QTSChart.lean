module

public import CFSG.LargeExtraspecial.AS35QTSEnc
public import CFSG.LargeExtraspecial.AS35QTSCheck
public import CFSG.LargeExtraspecial.AS35EFiveOne
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LargeExtraspecial.AS35QTS

open Subgroup CFSG.LargeExtraspecial.AS35QTh

variable {G : Type} [Group G] (S : Setting G)

structure Chart where
  th : G → Cd
  th_mul : ∀ x ∈ S.M, ∀ y ∈ S.M, th (x * y) = mulC (th x) (th y)
  th_injOn : ∀ x ∈ S.M, ∀ y ∈ S.M, th x = th y → x = y
  th_mem : ∀ x ∈ S.M, th x ∈ codes
  th_surj : ∀ c ∈ codes, ∃ x ∈ S.M, th x = c

@[expose] noncomputable def chartOf (φ : S.M ≃* CC) : Chart S := by
  classical
  exact
    { th := fun x => if h : x ∈ S.M then psiCode (φ ⟨x, h⟩) else e0
      th_mul := fun x hx y hy => by
        rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left (S.M.mul_mem hx hy), ← psiCode_mul,
          ← map_mul]
        rfl
      th_injOn := fun x hx y hy h => by
        rw [dite_eq_left hx, dite_eq_left hy] at h
        exact congrArg Subtype.val (φ.injective (psiCode_injective h))
      th_mem := fun x hx => by
        rw [dite_eq_left hx]
        exact psiCode_mem _
      th_surj := fun c hc => by
        obtain ⟨y, hy⟩ := exists_psiCode_eq hc
        refine ⟨(φ.symm y : G), (φ.symm y).2, ?_⟩
        rw [dite_eq_left (φ.symm y).2]
        simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply]
        exact hy }

theorem mm_I3_left (B : M3) : mm I3 B = B := by
  obtain ⟨⟨a, b, c⟩, ⟨d, e, f⟩, ⟨g, h, i⟩⟩ := B
  simp [mm, rowMul, dot, col0, col1, col2, I3]

theorem mm_I3_right (B : M3) : mm B I3 = B := by
  obtain ⟨⟨a, b, c⟩, ⟨d, e, f⟩, ⟨g, h, i⟩⟩ := B
  simp [mm, rowMul, dot, col0, col1, col2, I3]

theorem conj_ne_one {x : G} (hxz : IsConj S.z x) : x ≠ 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxz
  intro h
  apply S.z_ne_one
  calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
    _ = 1 := by rw [h]; group

namespace Chart

variable {S} (T : Chart S)

theorem th_comm {x y : G} (hx : x ∈ S.M) (hy : y ∈ S.M) :
    x * y = y * x ↔ mulC (T.th x) (T.th y) = mulC (T.th y) (T.th x) := by
  rw [← T.th_mul x hx y hy, ← T.th_mul y hy x hx]
  exact ⟨fun h => by rw [h], fun h => T.th_injOn _ (S.M.mul_mem hx hy) _ (S.M.mul_mem hy hx) h⟩

section

theorem e0_mem : e0 ∈ codes := mem_codes.mpr qts_small.1

theorem tau0_mem : tau0 ∈ codes := mem_codes.mpr qts_small.1

theorem th_one : T.th 1 = e0 := by
  obtain ⟨x, hx, hxe⟩ := T.th_surj e0 e0_mem
  have h1 : T.th (x * x) = T.th x := by rw [T.th_mul x hx x hx, hxe, qts_small.2.1]
  have h2 : x * x = x := T.th_injOn _ (S.M.mul_mem hx hx) x hx h1
  have h3 : x = 1 := by
    calc x = x * x * x⁻¹ := by group
      _ = 1 := by rw [h2, mul_inv_cancel]
  rw [← h3, hxe]

theorem th_eq_e0_iff {x : G} (hx : x ∈ S.M) : T.th x = e0 ↔ x = 1 := by
  constructor
  · intro h
    exact T.th_injOn x hx 1 S.M.one_mem (h.trans T.th_one.symm)
  · rintro rfl
    exact T.th_one

theorem th_pow {x : G} (hx : x ∈ S.M) (n : ℕ) : T.th (x ^ n) = powC (T.th x) n := by
  induction n with
  | zero => rw [pow_zero, T.th_one]; rfl
  | succ n ih =>
    rw [pow_succ, T.th_mul _ (S.M.pow_mem hx n) x hx, ih]
    rfl

theorem th_mem_il {x : G} (hx : x ∈ S.M) (h2 : x * x = 1) (h1 : x ≠ 1) : T.th x ∈ il := by
  refine mem_il.mpr ⟨T.th_mem x hx, ?_, fun h => h1 ((T.th_eq_e0_iff hx).mp h)⟩
  rw [← T.th_mul x hx x hx, h2, T.th_one]

theorem mul_self_of_mem_il {x : G} (hx : x ∈ S.M) (h : T.th x ∈ il) : x * x = 1 ∧ x ≠ 1 := by
  obtain ⟨-, h2, h1⟩ := mem_il.mp h
  refine ⟨(T.th_eq_e0_iff (S.M.mul_mem hx hx)).mp (by rw [T.th_mul x hx x hx, h2]), fun h => ?_⟩
  exact h1 ((T.th_eq_e0_iff hx).mpr h)

theorem th_z : T.th S.z = tau0 := by
  have hz : S.z ∈ S.M := S.zM.2
  have hg : ∀ g ∈ cgens, mulC (T.th S.z) g = mulC g (T.th S.z) := by
    intro g hg
    obtain ⟨y, hy, rfl⟩ := T.th_surj g (mem_codes.mpr (qts_small.2.2 g hg))
    exact (T.th_comm hz hy).mp (S.mem_M_iff.mp hy).symm
  rcases qts_center _ (T.th_mem _ hz) hg with h | h
  · exact absurd ((T.th_eq_e0_iff hz).mp h) S.z_ne_one
  · exact h

theorem th_inv_m {x : G} (hx : x ∈ S.M) : mm (T.th x).m (T.th x⁻¹).m = I3 := by
  have h := T.th_mul x hx x⁻¹ (S.M.inv_mem hx)
  rw [mul_inv_cancel, T.th_one] at h
  exact (congrArg Cd.m h).symm

@[expose] def qSub : Subgroup S.M where
  carrier := {x | (T.th x).m = I3}
  mul_mem' {x y} hx hy := by
    change (T.th ((x : G) * y)).m = I3
    rw [T.th_mul _ x.2 _ y.2]
    change mm (T.th x).m (T.th y).m = I3
    rw [hx, hy, mm_I3_left]
  one_mem' := by
    change (T.th 1).m = I3
    rw [T.th_one]
    rfl
  inv_mem' {x} hx := by
    change (T.th ((x : G)⁻¹)).m = I3
    have h := T.th_inv_m x.2
    change (T.th x).m = I3 at hx
    rwa [hx, mm_I3_left] at h

theorem qSub_normal : (T.qSub).Normal := by
  refine ⟨fun x hx m => ?_⟩
  change (T.th ((m : G) * x * (m : G)⁻¹)).m = I3
  change (T.th x).m = I3 at hx
  have hmx : (m : G) * x ∈ S.M := S.M.mul_mem m.2 x.2
  rw [T.th_mul _ hmx _ (S.M.inv_mem m.2), T.th_mul _ m.2 _ x.2]
  change mm (mm (T.th m).m (T.th x).m) (T.th (m : G)⁻¹).m = I3
  rw [hx, mm_I3_right, T.th_inv_m m.2]

theorem qSub_isPGroup : IsPGroup 2 T.qSub := by
  intro x
  refine ⟨2, ?_⟩
  have hx : (T.th x).m = I3 := x.2
  have h4 : T.th (((x : S.M) : G) ^ 4) = e0 := by
    rw [T.th_pow (x : S.M).2, qts_q_pow _ (T.th_mem _ (x : S.M).2) hx]
  have h4' : ((x : S.M) : G) ^ 4 = 1 := (T.th_eq_e0_iff (S.M.pow_mem (x : S.M).2 4)).mp h4
  apply Subtype.ext
  apply Subtype.ext
  simpa using h4'

theorem mem_QG_of_m {x : G} (hx : x ∈ S.M) (hm : (T.th x).m = I3) : x ∈ S.QG := by
  have hle := S.le_of_normal T.qSub T.qSub_normal T.qSub_isPGroup
  exact S.mem_QG_iff.mpr ⟨hx, hle (show (T.th x).m = I3 from hm)⟩

theorem eq_z_of_m (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {x : G}
    (hxz : IsConj S.z x) (hx : x ∈ S.M) (hm : (T.th x).m = I3) : x = S.z := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxz
  exact hW g (T.mem_QG_of_m hx hm)

theorem th_mem_sl (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {x : G}
    (hx : x ∈ S.M) (hxz : IsConj S.z x) (hne : x ≠ S.z) : T.th x ∈ sl := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxz
  have hxx := S.mul_self_of_isConj hxz
  have hil := T.th_mem_il hx hxx (conj_ne_one S hxz)
  refine mem_sl.mpr ⟨hil, fun hm => hne (T.eq_z_of_m hW hxz hx hm), ?_⟩
  set y := g⁻¹ * S.z * g with hy
  have hyz : IsConj S.z y := isConj_iff.mpr ⟨g⁻¹, by rw [hy, inv_inv]⟩
  have hyM : y ∈ S.M := by
    rw [S.mem_M_iff]
    have h1 := S.mem_M_iff.mp hx
    calc y * S.z = g⁻¹ * (S.z * (g * S.z * g⁻¹)) * g := by rw [hy]; group
      _ = g⁻¹ * ((g * S.z * g⁻¹) * S.z) * g := by rw [h1]
      _ = S.z * y := by rw [hy]; group
  have hyne : y ≠ S.z := by
    intro h
    apply hne
    calc g * S.z * g⁻¹ = g * y * g⁻¹ := by rw [h]
      _ = S.z := by rw [hy]; group
  have hyil := T.th_mem_il hyM (S.mul_self_of_isConj hyz) (conj_ne_one S hyz)
  obtain ⟨q', hq', -, hq2, hqc⟩ :=
    qts_root _ hyil (fun hm => hyne (T.eq_z_of_m hW hyz hyM hm))
  obtain ⟨q, hqM, rfl⟩ := T.th_surj q' hq'
  have hqq : q * q = S.z := by
    apply T.th_injOn _ (S.M.mul_mem hqM hqM) S.z S.zM.2
    rw [T.th_mul q hqM q hqM, hq2, T.th_z]
  have hqy : q * y = y * q := (T.th_comm hqM hyM).mpr hqc
  refine ⟨T.th (g * q * g⁻¹), ?_, ?_⟩
  · refine T.th_mem _ (S.mem_M_iff.mpr ?_)
    calc g * q * g⁻¹ * S.z = g * (q * y) * g⁻¹ := by rw [hy]; group
      _ = g * (y * q) * g⁻¹ := by rw [hqy]
      _ = S.z * (g * q * g⁻¹) := by rw [hy]; group
  · have hqM' : g * q * g⁻¹ ∈ S.M := by
      rw [S.mem_M_iff]
      calc g * q * g⁻¹ * S.z = g * (q * y) * g⁻¹ := by rw [hy]; group
        _ = g * (y * q) * g⁻¹ := by rw [hqy]
        _ = S.z * (g * q * g⁻¹) := by rw [hy]; group
    rw [← T.th_mul _ hqM' _ hqM']
    congr 1
    calc g * q * g⁻¹ * (g * q * g⁻¹) = g * (q * q) * g⁻¹ := by group
      _ = g * S.z * g⁻¹ := by rw [hqq]

theorem t0c_mem_sl : t0c ∈ sl := by
  have h := qts_lists.2.2.1
  unfold t0c
  cases hsl : sl with
  | nil => rw [hsl] at h; exact absurd h (by decide)
  | cons a l => exact List.mem_cons_self

theorem exists_conj_t0 {x : G} (hx : x ∈ S.M) (hxt : T.th x ∈ sl) :
    ∃ m ∈ S.M, ∃ τ₀ ∈ S.M, T.th τ₀ = t0c ∧ m * τ₀ * m⁻¹ = x := by
  obtain ⟨c, hc, hct⟩ := qts_class _ hxt
  obtain ⟨m, hm, rfl⟩ := T.th_surj c hc
  obtain ⟨τ₀, hτ₀, hτ₀t⟩ := T.th_surj t0c (mem_il.mp (mem_sl.mp t0c_mem_sl).1).1
  refine ⟨m, hm, τ₀, hτ₀, hτ₀t, ?_⟩
  have h1 : m * τ₀ = x * m := by
    apply T.th_injOn _ (S.M.mul_mem hm hτ₀) _ (S.M.mul_mem hx hm)
    rw [T.th_mul _ hm _ hτ₀, T.th_mul _ hx _ hm, hτ₀t, hct]
  calc m * τ₀ * m⁻¹ = x * m * m⁻¹ := by rw [h1]
    _ = x := by group

theorem exists_conj_of_mem_sl {x x' : G} (hx : x ∈ S.M) (hxt : T.th x ∈ sl) (hx' : x' ∈ S.M)
    (hxt' : T.th x' ∈ sl) : ∃ m ∈ S.M, m * x * m⁻¹ = x' := by
  obtain ⟨m, hm, τ₀, hτ₀, hτ, rfl⟩ := T.exists_conj_t0 hx hxt
  obtain ⟨m', hm', τ₁, hτ₁, hτ', rfl⟩ := T.exists_conj_t0 hx' hxt'
  have hτe : τ₀ = τ₁ := T.th_injOn _ hτ₀ _ hτ₁ (hτ.trans hτ'.symm)
  subst hτe
  refine ⟨m' * m⁻¹, S.M.mul_mem hm' (S.M.inv_mem hm), ?_⟩
  group

end

end Chart

end CFSG.LargeExtraspecial.AS35QTS
