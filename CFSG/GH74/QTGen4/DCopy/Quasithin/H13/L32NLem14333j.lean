module

public import CFSG.Quasithin.H13.L32NLem14333j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14333h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14333i

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits CFSG.Quasithin.SL3Model
open scoped commutatorElement MatrixGroups

namespace L14333

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx_F4
open CFSG.Quasithin.H13.L14333.Ctx_F4

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx_F4 G T L V V₂ K g a z b d x D)
include c

theorem schur_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) (σ : G → G)
    (hσV : ∀ v ∈ V, σ v ∈ V) (hσmul : ∀ v ∈ V, ∀ w ∈ V, σ (v * w) = σ v * σ w)
    (hσU : ∀ u ∈ fsuU T V, ∀ v ∈ V, σ (u * v * u⁻¹) = u * σ v * u⁻¹)
    (hσx : ∀ v ∈ V, σ (x * v * x⁻¹) = x * σ v * x⁻¹) :
    (∀ v ∈ V, σ v = 1) ∨ (∀ v ∈ V, σ v = v) := by
  obtain ⟨θ, ψ, -, hker, hequiv, hline, -, hQv⟩ := c.exists_coordZ_F4 hyp
  let σV : ↥V → ↥V := fun v => ⟨σ v, hσV v v.2⟩
  let f : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) := fun w =>
    Multiplicative.toAdd (ψ (σV (ψ.symm (Multiplicative.ofAdd w))))
  have hf : ∀ v : ↥V, f (Multiplicative.toAdd (ψ v)) = Multiplicative.toAdd (ψ (σV v)) := by
    intro v
    simp only [f, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  have hsurj : ∀ w : Fin 3 → ZMod 2, ∃ v : ↥V, Multiplicative.toAdd (ψ v) = w := fun w =>
    ⟨ψ.symm (Multiplicative.ofAdd w), by simp⟩
  have hfadd : ∀ w w', f (w + w') = f w + f w' := by
    intro w w'
    obtain ⟨v, rfl⟩ := hsurj w
    obtain ⟨v', rfl⟩ := hsurj w'
    rw [← toAdd_mul, ← map_mul, hf, hf, hf, ← toAdd_mul, ← map_mul]
    congr 2
    exact Subtype.ext (hσmul _ v.2 _ v'.2)
  have hf0 : f 0 = 0 := by
    have h := hfadd 0 0
    rw [add_zero] at h
    have h' : f 0 + 0 = f 0 + f 0 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  let F : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    { toFun := f
      map_add' := hfadd
      map_smul' := fun e w => by
        rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) e with rfl | rfl
        · simp only [zero_smul, RingHom.id_apply, hf0]
        · simp only [one_smul, RingHom.id_apply] }
  set M := LinearMap.toMatrix' F with hMdef
  have hM : ∀ w, M.mulVec w = f w := fun w => LinearMap.toMatrix'_mulVec F w

  have hcomm : ∀ l : ↥L, (∀ v ∈ V, σ ((l : G) * v * (l : G)⁻¹) = (l : G) * σ v * (l : G)⁻¹) →
      M * (θ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        (θ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M := by
    intro l hl
    rw [Matrix.ext_iff_mulVec]
    intro w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, hM]
    obtain ⟨v, rfl⟩ := hsurj w
    have h1 : (θ l : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (ψ v)) =
        Multiplicative.toAdd (ψ ⟨(l : G) * v * (l : G)⁻¹, c.conj_mem_V_F4 l.2 v.2⟩) :=
      (hequiv l v).symm
    have h2 : (θ l : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (ψ (σV v))) =
        Multiplicative.toAdd (ψ ⟨(l : G) * σ v * (l : G)⁻¹, c.conj_mem_V_F4 l.2 (hσV v v.2)⟩) :=
      (hequiv l (σV v)).symm
    rw [h1, hf ⟨_, _⟩, hf v, h2]
    congr 2
    exact Subtype.ext (hl v v.2)

  have hz : Multiplicative.toAdd (ψ ⟨z, c.z_mem_V_F4⟩) = vE (ZMod 2) 0 := by
    obtain ⟨e, he⟩ := (hline ⟨z, c.z_mem_V_F4⟩).mp c.z_mem
    have he1 : e ≠ 0 := by
      rintro rfl
      apply c.z_ne
      rw [zero_smul] at he
      have h1 : ψ ⟨z, c.z_mem_V_F4⟩ = 1 := Multiplicative.toAdd.injective he
      exact congrArg Subtype.val (ψ.injective (h1.trans (map_one ψ).symm))
    have he' : e = 1 := (by decide : ∀ e : ZMod 2, e ≠ 0 → e = 1) e he1
    rw [he, he', one_smul]

  have hx3 : θ ⟨x, c.x_mem⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, c.x_mem⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using c.x_cube)
    rw [this, map_one]
  have hx1 : θ ⟨x, c.x_mem⟩ ≠ 1 := fun h =>
    c.x_ne_one_F4 (eq_one_of_mem_pCoreOf ((hker _).mp h) (by decide : Odd 3) c.x_cube)
  have hxe : θ ⟨x, c.x_mem⟩ • vE (ZMod 2) 0 = vE (ZMod 2) 0 := by
    rw [← hz, ← hequiv ⟨x, c.x_mem⟩]
    congr 2
    exact Subtype.ext c.x_z
  obtain ⟨b', c', k, hy0⟩ := sl3_y0_mem (θ ⟨x, c.x_mem⟩) hx3 hx1 hxe
  have hMq : ∀ b c : ZMod 2, M * (tq b c : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (tq b c : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M := by
    intro b₀ c₀
    obtain ⟨u, hu, hθu⟩ := hQv (tq b₀ c₀) (tq_mem_Qv b₀ c₀)
    rw [← hθu]
    exact hcomm u (fun v hv => hσU u hu v hv)
  have hMx : Commute M (θ ⟨x, c.x_mem⟩ : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
    hcomm ⟨x, c.x_mem⟩ (fun v hv => hσx v hv)
  have hMy : M * (y0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (y0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M := by
    rw [hy0, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow]
    exact ((show Commute M (tq b' c' : Matrix (Fin 3) (Fin 3) (ZMod 2)) from hMq b' c').mul_right
      (hMx.pow_right (k : ℕ))).eq
  rcases sl3_comm_A4 M hMq hMy with h0 | h1
  · left
    intro v hv
    have h := hM (Multiplicative.toAdd (ψ ⟨v, hv⟩))
    rw [h0, Matrix.zero_mulVec, hf] at h
    have h' : ψ (σV ⟨v, hv⟩) = 1 := Multiplicative.toAdd.injective h.symm
    exact congrArg Subtype.val (ψ.injective (h'.trans (map_one ψ).symm))
  · right
    intro v hv
    have h := hM (Multiplicative.toAdd (ψ ⟨v, hv⟩))
    rw [h1, Matrix.one_mulVec, hf] at h
    exact congrArg Subtype.val (ψ.injective (Multiplicative.toAdd.injective h.symm))

theorem comm_V_of_mem_Q_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {r : G}
    (hr : r ∈ pCoreOf 2 (l32nH T V)) (hrx : r * x = x * r) : ∀ v ∈ V, r * v = v * r := by
  obtain ⟨_, S⟩ := c.setting
  have hrH : r ∈ l32nH T V := pCoreOf_le 2 _ hr
  have hrV : ∀ v ∈ V, r * v * r⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (S.TV_F4 (c.q_le hr)) v).mp hv
  have hσU : ∀ u ∈ fsuU T V, ∀ v ∈ V,
      r * (u * v * u⁻¹) * r⁻¹ = u * (r * v * r⁻¹) * u⁻¹ := by
    intro u hu v hv
    set e := r * u * r⁻¹ * u⁻¹ with he
    have heV : e ∈ fsuV1 T V := c.comm_Q_U_mem_F4 hr hu
    have huH : u ∈ l32nH T V := c.ctx.U_le hu
    have hvH : r * v * r⁻¹ ∈ l32nH T V := c.ctx.U_le (c.ctx.V_U (hrV v hv))
    have hm : u * (r * v * r⁻¹) * u⁻¹ ∈ l32nH T V := mul_mem (mul_mem huH hvH) (inv_mem huH)
    have hce := c.ctx.H_V1 _ hm e heV
    have hem : e * (u * (r * v * r⁻¹) * u⁻¹) = (u * (r * v * r⁻¹) * u⁻¹) * e := by
      calc e * (u * (r * v * r⁻¹) * u⁻¹)
          = (u * (r * v * r⁻¹) * u⁻¹ * e * (u * (r * v * r⁻¹) * u⁻¹)⁻¹) *
            (u * (r * v * r⁻¹) * u⁻¹) := by rw [hce]
        _ = (u * (r * v * r⁻¹) * u⁻¹) * e := by group
    calc r * (u * v * u⁻¹) * r⁻¹ = e * (u * (r * v * r⁻¹) * u⁻¹) * e⁻¹ := by rw [he]; group
      _ = u * (r * v * r⁻¹) * u⁻¹ := by rw [hem]; group
  have hσx : ∀ v ∈ V, r * (x * v * x⁻¹) * r⁻¹ = x * (r * v * r⁻¹) * x⁻¹ := by
    intro v _
    calc r * (x * v * x⁻¹) * r⁻¹ = (r * x) * v * (r * x)⁻¹ := by group
      _ = (x * r) * v * (x * r)⁻¹ := by rw [hrx]
      _ = x * (r * v * r⁻¹) * x⁻¹ := by group
  rcases c.schur_F4 hyp (fun v => r * v * r⁻¹) hrV (fun v _ w _ => by group) hσU hσx with h | h
  · exact (c.z_ne ((c.ctx.H_V1 r hrH z c.z_mem).symm.trans (h z c.z_mem_V_F4))).elim
  · intro v hv
    calc r * v = r * v * r⁻¹ * r := by group
      _ = v * r := by rw [h v hv]

theorem comm_mem_P_of_comm_V_F4 {r : G} (hr : r ∈ T) (hrV : ∀ v ∈ V, r * v = v * r) {l : G}
    (hl : l ∈ L) : r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  obtain ⟨_, S⟩ := c.setting
  rw [← S.cent_eq_F4]
  refine ⟨L.mul_mem ((Subgroup.mem_normalizer_iff.mp (c.T_le_normL_F4 hr) l).mp hl) (L.inv_mem hl),
    Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  have hw : l⁻¹ * v * l ∈ V := by
    have := c.conj_mem_V_F4 (L.inv_mem hl) hv
    rwa [inv_inv] at this
  have h1 : r⁻¹ * (l⁻¹ * v * l) * r = l⁻¹ * v * l := by
    rw [mul_assoc, ← hrV _ hw]; group
  have h2 : r * l * r⁻¹ * l⁻¹ * v * (r * l * r⁻¹ * l⁻¹)⁻¹ = v := by
    calc r * l * r⁻¹ * l⁻¹ * v * (r * l * r⁻¹ * l⁻¹)⁻¹ =
          r * l * (r⁻¹ * (l⁻¹ * v * l) * r) * l⁻¹ * r⁻¹ := by group
      _ = r * v * r⁻¹ := by rw [h1]; group
      _ = v := by rw [hrV v hv]; group
  calc v * (r * l * r⁻¹ * l⁻¹) =
        (r * l * r⁻¹ * l⁻¹ * v * (r * l * r⁻¹ * l⁻¹)⁻¹) * (r * l * r⁻¹ * l⁻¹) := by rw [h2]
    _ = r * l * r⁻¹ * l⁻¹ * v := by group

theorem inv_P_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {r : G} (hr : r ∈ T)
    (hrV : ∀ v ∈ V, r * v = v * r) (hrd : r * d * r⁻¹ = d⁻¹) :
    ∀ p ∈ pCoreOf 2 L, r * p * r⁻¹ = p⁻¹ := by
  obtain ⟨hP, -⟩ := c.pCoreOf_eq_F4 hyp
  have hPab : ∀ u ∈ pCoreOf 2 L, ∀ w ∈ pCoreOf 2 L, u * w = w * u := hP ▸ c.X_comm_F4
  have hsqV : ∀ u ∈ pCoreOf 2 L, u * u ∈ V := hP ▸ c.sq_mem_V_of_X_F4
  have hdP : d ∈ pCoreOf 2 L := (le_sup_right.trans (c.sup_zU_le_P_F4 hyp)) c.d_mem
  have hLP : ∀ l ∈ L, ∀ p ∈ pCoreOf 2 L, l * p * l⁻¹ ∈ pCoreOf 2 L := fun l hl p hp =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hl) p).mp hp

  have hinv : ∀ l ∈ L, ∀ p ∈ pCoreOf 2 L, r * p * r⁻¹ = p⁻¹ →
      r * (l * p * l⁻¹) * r⁻¹ = (l * p * l⁻¹)⁻¹ := by
    intro l hl p hp hrp
    have hk := c.comm_mem_P_of_comm_V_F4 hr hrV hl
    set k := r * l * r⁻¹ * l⁻¹ with hk'
    calc r * (l * p * l⁻¹) * r⁻¹ = k * (l * (r * p * r⁻¹) * l⁻¹) * k⁻¹ := by rw [hk']; group
      _ = k * (l * p⁻¹ * l⁻¹) * k⁻¹ := by rw [hrp]
      _ = l * p⁻¹ * l⁻¹ * k * k⁻¹ := by rw [hPab k hk _ (hLP l hl _ (inv_mem hp))]
      _ = (l * p * l⁻¹)⁻¹ := by group

  have hW : ∀ v ∈ V, ∃ p ∈ pCoreOf 2 L, r * p * r⁻¹ = p⁻¹ ∧ p * p = v := by
    intro v hv
    by_cases hv1 : v = 1
    · exact ⟨1, one_mem _, by group, by rw [hv1]; group⟩
    obtain ⟨l, hl, rfl⟩ := c.exists_conj_eq_F4 hyp hv hv1
    exact ⟨l * d * l⁻¹, hLP l hl d hdP, hinv l hl d hdP hrd, by rw [← c.d_sq]; group⟩
  intro p hp
  obtain ⟨q, hq, hrq, hqq⟩ := hW (p * p) (hsqV p hp)
  have hpq : p * q⁻¹ ∈ V := by
    refine c.mem_V_of_mul_self_F4 hyp (mul_mem hp (inv_mem hq)) ?_
    have hc := hPab p hp q⁻¹ (inv_mem hq)
    calc p * q⁻¹ * (p * q⁻¹) = p * (q⁻¹ * p) * q⁻¹ := by group
      _ = p * (p * q⁻¹) * q⁻¹ := by rw [← hc]
      _ = (p * p) * (q * q)⁻¹ := by group
      _ = 1 := by rw [hqq]; group
  have h1 : r * (p * q⁻¹) * r⁻¹ = p * q⁻¹ := by rw [hrV _ hpq]; group
  calc r * p * r⁻¹ = (r * (p * q⁻¹) * r⁻¹) * (r * q * r⁻¹) := by group
    _ = p⁻¹ * (p * p) * q⁻¹ * q⁻¹ := by rw [h1, hrq]; group
    _ = p⁻¹ := by rw [← hqq]; group

theorem not_mem_L_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {r : G}
    (hrV : ∀ v ∈ V, r * v = v * r) (hrd : r * d * r⁻¹ = d⁻¹) : r ∉ L := by
  obtain ⟨_, S⟩ := c.setting
  obtain ⟨hP, -⟩ := c.pCoreOf_eq_F4 hyp
  have hPab : ∀ u ∈ pCoreOf 2 L, ∀ w ∈ pCoreOf 2 L, u * w = w * u := hP ▸ c.X_comm_F4
  have hdP : d ∈ pCoreOf 2 L := (le_sup_right.trans (c.sup_zU_le_P_F4 hyp)) c.d_mem
  intro hrL
  have hrP : r ∈ pCoreOf 2 L := by
    rw [← S.cent_eq_F4]
    exact ⟨hrL, Subgroup.mem_centralizer_iff.mpr fun v hv => (hrV v hv).symm⟩
  have h1 : d = d⁻¹ := by rw [← hrd, hPab r hrP d hdP]; group
  apply c.z_ne
  rw [← c.d_sq]
  calc d * d = d * d⁻¹ := by rw [← h1]
    _ = 1 := mul_inv_cancel d

theorem exists_inv_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {r : G}
    (hr : r ∈ pCoreOf 2 (l32nH T V)) (hrx : r * x = x * r) (hrd : r * d * r⁻¹ = d⁻¹) :
    ∃ r' ∈ pCoreOf 2 (l32nH T V), r' * x = x * r' ∧ r' * d * r'⁻¹ = d⁻¹ ∧
      (∀ v ∈ V, r' * v = v * r') ∧ (∀ p ∈ pCoreOf 2 L, r' * p * r'⁻¹ = p⁻¹) ∧
      (∀ l ∈ L, r' * l * r'⁻¹ * l⁻¹ ∈ V) ∧ r' * r' = 1 := by
  obtain ⟨hP, -⟩ := c.pCoreOf_eq_F4 hyp
  have hPab : ∀ u ∈ pCoreOf 2 L, ∀ w ∈ pCoreOf 2 L, u * w = w * u := hP ▸ c.X_comm_F4
  have hsqV : ∀ u ∈ pCoreOf 2 L, u * u ∈ V := hP ▸ c.sq_mem_V_of_X_F4
  have hLP : ∀ l ∈ L, ∀ p ∈ pCoreOf 2 L, l * p * l⁻¹ ∈ pCoreOf 2 L := fun l hl p hp =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hl) p).mp hp
  have hrT : r ∈ T := c.q_le hr
  have hrV := c.comm_V_of_mem_Q_F4 hyp hr hrx
  have hrP := c.inv_P_F4 hyp hrT hrV hrd
  have he : ∀ l ∈ L, r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 L := fun l hl =>
    c.comm_mem_P_of_comm_V_F4 hrT hrV hl

  obtain ⟨w₁, hw₁, hf₁⟩ := c.cocycle_V_F4 hyp (fun l => (r * l * r⁻¹ * l⁻¹) * (r * l * r⁻¹ * l⁻¹))
    (fun l hl => hsqV _ (he l hl)) (fun l₁ hl₁ l₂ hl₂ => sq_comm_mul hPab hLP he hl₁ hl₂)
    (fun p hp => by
      show r * p * r⁻¹ * p⁻¹ * (r * p * r⁻¹ * p⁻¹) = 1
      rw [hrP p hp]
      have h4 := c.mul_self_V_F4 (hsqV p hp)
      calc p⁻¹ * p⁻¹ * (p⁻¹ * p⁻¹) = (p * p * (p * p))⁻¹ := by group
        _ = 1 := by rw [h4, inv_one])
    (fun u hu => c.mul_self_V_F4 (Subgroup.mem_inf.mp (c.comm_Q_U_mem_F4 hr hu)).1)
    (by show r * x * r⁻¹ * x⁻¹ * (r * x * r⁻¹ * x⁻¹) = 1; rw [hrx]; group)

  obtain ⟨d₁, hd₁, hd₁w⟩ : ∃ d₁ ∈ centerOf (fsuU T V), d₁ * d₁ = w₁ := by
    rcases c.eq_of_mem_V1_F4 hw₁ with rfl | rfl
    · exact ⟨1, Subgroup.one_mem _, mul_one 1⟩
    · exact ⟨d, c.d_mem, c.d_sq⟩
  have hd₁P : d₁ ∈ pCoreOf 2 L := (le_sup_right.trans (c.sup_zU_le_P_F4 hyp)) hd₁
  have hdP : d ∈ pCoreOf 2 L := (le_sup_right.trans (c.sup_zU_le_P_F4 hyp)) c.d_mem
  have hd₁U : d₁ ∈ fsuU T V := (Subgroup.mem_inf.mp hd₁).1
  have hd₁V : ∀ v ∈ V, d₁ * v = v * d₁ := fun v hv =>
    (Subgroup.mem_centralizer_iff.mp (c.P_le_centralizer_F4 hd₁P) v hv).symm
  set r' := r * d₁ with hr'
  have hr'Q : r' ∈ pCoreOf 2 (l32nH T V) := mul_mem hr (fsuU_le_pCoreOf c.ctx hd₁U)
  have hr'T : r' ∈ T := c.q_le hr'Q
  have hr'V : ∀ v ∈ V, r' * v = v * r' := by
    intro v hv
    rw [hr', mul_assoc, hd₁V v hv, ← mul_assoc, hrV v hv, mul_assoc]
  have hr'P : ∀ p ∈ pCoreOf 2 L, r' * p * r'⁻¹ = p⁻¹ := by
    intro p hp
    have h1 : d₁ * p * d₁⁻¹ = p := by rw [hPab d₁ hd₁P p hp]; group
    calc r' * p * r'⁻¹ = r * (d₁ * p * d₁⁻¹) * r⁻¹ := by rw [hr']; group
      _ = p⁻¹ := by rw [h1, hrP p hp]
  have hr'x : r' * x = x * r' := by
    have h1 : d₁ * x = x * d₁ := by
      calc d₁ * x = (x * d₁ * x⁻¹) * x := by rw [c.x_comm_zU_F4 hd₁]
        _ = x * d₁ := by group
    rw [hr', mul_assoc, h1, ← mul_assoc, hrx, mul_assoc]
  have hr'd : r' * d * r'⁻¹ = d⁻¹ := hr'P d hdP

  have hr'L : ∀ l ∈ L, r' * l * r'⁻¹ * l⁻¹ ∈ V := by
    intro l hl
    refine c.mem_V_of_mul_self_F4 hyp (c.comm_mem_P_of_comm_V_F4 hr'T hr'V hl) ?_
    have hA : l * d₁ * l⁻¹ * d₁⁻¹ ∈ pCoreOf 2 L := mul_mem (hLP l hl d₁ hd₁P) (inv_mem hd₁P)
    have hq : d₁ * l * d₁⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
      rw [show d₁ * l * d₁⁻¹ * l⁻¹ = d₁ * (l * d₁⁻¹ * l⁻¹) by group]
      exact mul_mem hd₁P (hLP l hl _ (inv_mem hd₁P))
    have e1 : r' * l * r'⁻¹ * l⁻¹ = (l * d₁ * l⁻¹ * d₁⁻¹) * (r * l * r⁻¹ * l⁻¹) := by
      have h1 := hrP _ hq
      calc r' * l * r'⁻¹ * l⁻¹ = r * (d₁ * l * d₁⁻¹ * l⁻¹) * r⁻¹ * (r * l * r⁻¹ * l⁻¹) := by
            rw [hr']; group
        _ = (d₁ * l * d₁⁻¹ * l⁻¹)⁻¹ * (r * l * r⁻¹ * l⁻¹) := by rw [h1]
        _ = (l * d₁ * l⁻¹ * d₁⁻¹) * (r * l * r⁻¹ * l⁻¹) := by group
    rw [e1]
    set A := l * d₁ * l⁻¹ * d₁⁻¹ with hAdef
    set B := r * l * r⁻¹ * l⁻¹ with hBdef
    have hB := he l hl
    have hAB := hPab _ hA _ hB
    have hBB : B * B = w₁ * (l * w₁ * l⁻¹) := hf₁ l hl
    have hlw : l * w₁ * l⁻¹ ∈ V := c.conj_mem_V_F4 hl (Subgroup.mem_inf.mp hw₁).1
    have hAA : A * A = (l * w₁ * l⁻¹) * w₁⁻¹ := by
      have hc := hPab _ (hLP l hl d₁ hd₁P) _ (inv_mem hd₁P)
      calc A * A = l * d₁ * l⁻¹ * (d₁⁻¹ * (l * d₁ * l⁻¹)) * d₁⁻¹ := by rw [hAdef]; group
        _ = l * d₁ * l⁻¹ * ((l * d₁ * l⁻¹) * d₁⁻¹) * d₁⁻¹ := by rw [← hc]
        _ = (l * (d₁ * d₁) * l⁻¹) * (d₁ * d₁)⁻¹ := by group
        _ = (l * w₁ * l⁻¹) * w₁⁻¹ := by rw [hd₁w]
    calc A * B * (A * B) = A * (B * A) * B := by group
      _ = A * (A * B) * B := by rw [← hAB]
      _ = (A * A) * (B * B) := by group
      _ = (l * w₁ * l⁻¹) * (w₁⁻¹ * w₁) * (l * w₁ * l⁻¹) := by rw [hAA, hBB]; group
      _ = 1 := by rw [inv_mul_cancel, mul_one, c.mul_self_V_F4 hlw]

  have hsq : r' * r' ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨T.mul_mem hr'T hr'T, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have hk := hr'L l hl
    have hk2 := c.mul_self_V_F4 hk
    have h1 : r' * (r' * l * r'⁻¹ * l⁻¹) * r'⁻¹ = r' * l * r'⁻¹ * l⁻¹ := by
      rw [hr'V _ hk]; group
    have h2 : (r' * r') * l * (r' * r')⁻¹ = l := by
      calc (r' * r') * l * (r' * r')⁻¹ =
            r' * ((r' * l * r'⁻¹ * l⁻¹) * l) * r'⁻¹ := by group
        _ = (r' * (r' * l * r'⁻¹ * l⁻¹) * r'⁻¹) * (r' * l * r'⁻¹ * l⁻¹) * l := by group
        _ = (r' * l * r'⁻¹ * l⁻¹) * (r' * l * r'⁻¹ * l⁻¹) * l := by rw [h1]
        _ = l := by rw [hk2, one_mul]
    calc l * (r' * r') = (r' * r') * l * (r' * r')⁻¹ * (r' * r') := by rw [h2]
      _ = (r' * r') * l := by group
  rw [c.centralizer_L_eq_bot_F4 hyp, Subgroup.mem_bot] at hsq
  exact ⟨r', hr'Q, hr'x, hr'd, hr'V, hr'P, hr'L, hsq⟩

theorem exists_mul_comm_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {r : G}
    (hrP : ∀ p ∈ pCoreOf 2 L, r * p * r⁻¹ = p⁻¹) (hrL : ∀ l ∈ L, r * l * r⁻¹ * l⁻¹ ∈ V)
    {l : G} (hl : l ∈ L) : ∃ p ∈ pCoreOf 2 L, r * (p * l) = p * l * r := by
  obtain ⟨hP, -⟩ := c.pCoreOf_eq_F4 hyp
  obtain ⟨p, hp, hpp⟩ := c.exists_sq_F4 hyp.V_eq _ (hrL l hl)
  rw [← hP] at hp
  refine ⟨p, hp, ?_⟩
  have h1 : r * (p * l) * r⁻¹ = p * l := by
    calc r * (p * l) * r⁻¹ = (r * p * r⁻¹) * (r * l * r⁻¹ * l⁻¹) * l := by group
      _ = p⁻¹ * (p * p) * l := by rw [hrP p hp, ← hpp]
      _ = p * l := by group
  calc r * (p * l) = r * (p * l) * r⁻¹ * r := by group
    _ = p * l * r := by rw [h1]

end Ctx_F4

end L14333

end CFSG.Quasithin.H13
