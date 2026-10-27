module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.PhiMap
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathSplit

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThCyc.exists_eq_add_w_apply (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hτw : vConj hD t * w * vConj hD t = w + 1) (x : VSub hD) :
    ∃ a a' : VSub hD, a.val ∈ A ∧ a'.val ∈ A ∧ x = a + w a' := by
  let a' : VSub hD := (vConj hD t + 1) x
  have hτ : vConj hD t * vConj hD t = 1 := H.vConj_t_mul_self W W2 hD
  have hτw' : vConj hD t * w = (w + 1) * vConj hD t := by
    calc vConj hD t * w
        = (vConj hD t * w) * (vConj hD t * vConj hD t) := by rw [hτ, mul_one]
      _ = (vConj hD t * w * vConj hD t) * vConj hD t := by noncomm_ring
      _ = (w + 1) * vConj hD t := by rw [hτw]
  have hτa' : vConj hD t a' = a' := by
    dsimp only [a']
    calc vConj hD t ((vConj hD t + 1) x)
        = vConj hD t (vConj hD t x) +
            vConj hD t ((1 : AddMonoid.End (VSub hD)) x) := map_add _ _ _
      _ = (vConj hD t * vConj hD t) x + (vConj hD t * 1) x := rfl
      _ = (vConj hD t * vConj hD t + vConj hD t * 1) x := rfl
      _ = (1 + vConj hD t) x := by rw [hτ, mul_one]
      _ = vConj hD t x + x := by
          show x + vConj hD t x = vConj hD t x + x
          exact add_comm x _
      _ = (vConj hD t + 1) x := rfl
  have hterm : (vConj hD t + 1) (w a') = a' := by
    calc (vConj hD t + 1) (w a')
        = vConj hD t (w a') + (1 : AddMonoid.End (VSub hD)) (w a') := rfl
      _ = (vConj hD t * w) a' + w a' := rfl
      _ = ((w + 1) * vConj hD t) a' + w a' := by rw [hτw']
      _ = (w + 1) (vConj hD t a') + w a' := rfl
      _ = (w + 1) a' + w a' := by rw [hτa']
      _ = (w a' + (1 : AddMonoid.End (VSub hD)) a') + w a' := rfl
      _ = (w a' + a') + w a' := rfl
      _ = a' := by
          calc (w a' + a') + w a' = a' + (w a' + w a') := by abel
            _ = a' + 0 := by rw [VSub.add_self_apply hD (w a')]
            _ = a' := add_zero _
  have ha'A : a'.val ∈ A := by
    dsimp only [a']
    rw [H.val_vConj_t_add_one_apply W W2 hD]
    exact H.thV_mem_A W W2 hD (AbelianSub.val_mem x)
  let y : VSub hD := x + w a'
  have hNy : (vConj hD t + 1) y = 0 := by
    dsimp only [y]
    rw [map_add]
    change a' + (vConj hD t + 1) (w a') = 0
    rw [hterm, VSub.add_self_apply hD a']
  have hyA : y.val ∈ A := by
    have hval : thV t y.val = 1 := by
      have h := congrArg AbelianSub.val hNy
      rw [H.val_vConj_t_add_one_apply W W2 hD, AbelianSub.val_zero] at h
      exact h
    exact (H.thV_eq_one_iff W W2 hD (AbelianSub.val_mem y)).1 hval
  refine ⟨y, a', hyA, ha'A, ?_⟩
  dsimp only [y]
  rw [add_assoc, VSub.add_self_apply hD (w a'), add_zero]

theorem ThCyc.end_eq_of_commute_of_eq_on_A (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hτw : vConj hD t * w * vConj hD t = w + 1) {f f' : AddMonoid.End (VSub hD)}
    (hf : f * w = w * f) (hf' : f' * w = w * f')
    (h : ∀ x : VSub hD, x.val ∈ A → f x = f' x) : f = f' := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨a, a', ha, ha', hx⟩ := H.exists_eq_add_w_apply W W2 hD hτw x
  have hfw : f (w a') = w (f a') := by
    have h' := congrArg (fun e : AddMonoid.End (VSub hD) => e a') hf
    simpa only [AddMonoid.End.coe_mul, Function.comp_apply] using h'
  have hf'w : f' (w a') = w (f' a') := by
    have h' := congrArg (fun e : AddMonoid.End (VSub hD) => e a') hf'
    simpa only [AddMonoid.End.coe_mul, Function.comp_apply] using h'
  calc f x = f (a + w a') := by rw [hx]
    _ = f a + f (w a') := map_add (f : VSub hD →+ VSub hD) a (w a')
    _ = f' a + f' (w a') := by rw [h a ha, hfw, h a' ha', ← hf'w]
    _ = f' (a + w a') := (map_add (f' : VSub hD →+ VSub hD) a (w a')).symm
    _ = f' x := by rw [hx]

private theorem ThCyc.tau_mul_w (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hτw : vConj hD t * w * vConj hD t = w + 1) :
    vConj hD t * w = (w + 1) * vConj hD t := by
  have hτ : vConj hD t * vConj hD t = 1 := H.vConj_t_mul_self W W2 hD
  calc vConj hD t * w
      = (vConj hD t * w) * (vConj hD t * vConj hD t) := by rw [hτ, mul_one]
    _ = (vConj hD t * w * vConj hD t) * vConj hD t := by noncomm_ring
    _ = (w + 1) * vConj hD t := by rw [hτw]

private theorem ThCyc.tau_apply_of_mem_A (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {x : VSub hD} (hx : x.val ∈ A) :
    vConj hD t x = x := by
  apply AbelianSub.ext
  rw [val_vConj_apply hD (H.t_mem_normalizer_omega1 W W2 hD)]
  have hAL : x.val ∈ L := W.S_le ((W.mem_A_iff x.val).1 hx).1
  have hcomm : t * x.val = x.val * t := H.comm_of_mem_L hAL
  calc t * x.val * t⁻¹ = (x.val * t) * t⁻¹ := by rw [hcomm]
    _ = x.val := by group

private theorem ThCyc.vConj_mem_normalizer_omega1_of_mem_Hn (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {n : G}
    (hn : n ∈ L ⊓ normalizer (A : Set G)) :
    n ∈ normalizer (omega1 D hD.comm : Set G) := by
  have hn' : n ∈ normInL L A := ⟨hn.1, fun x hx => (mem_normalizer_iff.1 hn.2 x).1 hx⟩
  exact H.normalizer_le_normalizer_omega1 W W2 hD
    (H.mem_normalizer_W5_of_mem_normInL W W2 hD hn')

private theorem ThCyc.vConj_comm_tau_of_mem_Hn (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {n : G}
    (hn : n ∈ L ⊓ normalizer (A : Set G)) :
    vConj hD n * vConj hD t = vConj hD t * vConj hD n := by
  have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) :=
    ThCyc.vConj_mem_normalizer_omega1_of_mem_Hn H W W2 hD hn
  have htV : t ∈ normalizer (omega1 D hD.comm : Set G) :=
    H.t_mem_normalizer_omega1 W W2 hD
  have hnt : n * t = t * n := (H.comm_of_mem_L hn.1).symm
  calc vConj hD n * vConj hD t = vConj hD (n * t) := (vConj_mul hD hnV htV).symm
    _ = vConj hD (t * n) := by rw [hnt]
    _ = vConj hD t * vConj hD n := vConj_mul hD htV hnV

private theorem ThCyc.vConj_mul_self_eq_one_of_sq_fixes (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hτw : vConj hD t * w * vConj hD t = w + 1) {n : G}
    (hn : n ∈ L ⊓ normalizer (A : Set G))
    (hn2 : ∀ a ∈ A, n * (n * a * n⁻¹) * n⁻¹ = a) :
    vConj hD n * vConj hD n = 1 := by
  have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) :=
    ThCyc.vConj_mem_normalizer_omega1_of_mem_Hn H W W2 hD hn
  have hδw : vConj hD n * w = w * vConj hD n := hwH n hn
  have hf : (vConj hD n * vConj hD n) * w = w * (vConj hD n * vConj hD n) := by
    calc (vConj hD n * vConj hD n) * w
        = vConj hD n * (vConj hD n * w) := by noncomm_ring
      _ = vConj hD n * (w * vConj hD n) := by rw [hδw]
      _ = (vConj hD n * w) * vConj hD n := by noncomm_ring
      _ = (w * vConj hD n) * vConj hD n := by rw [hδw]
      _ = w * (vConj hD n * vConj hD n) := by noncomm_ring
  have hf' : (1 : AddMonoid.End (VSub hD)) * w = w * 1 := by rw [one_mul, mul_one]
  refine H.end_eq_of_commute_of_eq_on_A W W2 hD hτw hf hf' ?_
  intro x hx
  apply AbelianSub.ext
  change (vConj hD n (vConj hD n x)).val = x.val
  rw [val_vConj_apply hD hnV, val_vConj_apply hD hnV]
  exact hn2 x.val hx

private theorem ThCyc.add_one_mul_add_one_eq_zero (hD : DHyp A Aa t D)
    {d : AddMonoid.End (VSub hD)} (hd : d * d = 1) :
    (d + 1) * (d + 1) = 0 := by
  have h1 : (1 : AddMonoid.End (VSub hD)) + 1 = 0 := VSub.add_self hD 1
  calc (d + 1) * (d + 1) = d * d + d * 1 + 1 * d + 1 * 1 := by noncomm_ring
    _ = 1 + d + d + 1 := by rw [hd]; simp
    _ = 0 := by
        calc (1 : AddMonoid.End (VSub hD)) + d + d + 1 = (1 + 1) + (d + d) := by abel
          _ = 0 := by rw [h1, VSub.add_self hD d]; abel

private theorem ThCyc.one_add_mul_mul_self (hD : DHyp A Aa t D)
    {w e : AddMonoid.End (VSub hD)} (hee : e * e = 0) (hew : e * w = w * e) :
    (1 + w * e) * (1 + w * e) = 1 := by
  have hwe : (w * e) * (w * e) = 0 := by
    calc (w * e) * (w * e) = w * (e * w) * e := by noncomm_ring
      _ = w * (w * e) * e := by rw [hew]
      _ = (w * w) * (e * e) := by noncomm_ring
      _ = 0 := by rw [hee]; simp
  calc (1 + w * e) * (1 + w * e)
      = 1 + (w * e) + (w * e) + (w * e) * (w * e) := by noncomm_ring
    _ = 1 + ((w * e) + (w * e)) + (w * e) * (w * e) := by abel
    _ = 1 := by rw [VSub.add_self hD (w * e), hwe]; abel

private theorem ThCyc.one_add_w_mul_comm (hD : DHyp A Aa t D)
    {w e : AddMonoid.End (VSub hD)} (hew : e * w = w * e) :
    (1 + w * e) * w = w * (1 + w * e) := by
  calc (1 + w * e) * w = 1 * w + (w * e) * w := add_mul _ _ _
    _ = w + w * (e * w) := by rw [one_mul, mul_assoc]
    _ = w + w * (w * e) := by rw [hew]
    _ = w * (1 + w * e) := by rw [mul_add, mul_one]

private theorem ThCyc.delta_mul_one_add_w_eq (hD : DHyp A Aa t D)
    {τ d w : AddMonoid.End (VSub hD)} (hτ : τ * τ = 1) (hdτ : d * τ = τ * d)
    (hdw : d * w = w * d) (hτw' : τ * w = (w + 1) * τ) (hdd : d * d = 1) :
    d * (1 + w * (d + 1)) = τ * (1 + w * (d + 1)) * τ := by
  have hde : d * (d + 1) = d + 1 := by
    calc d * (d + 1) = d * d + d * 1 := by rw [mul_add, mul_one]
      _ = 1 + d := by rw [hdd, mul_one]
      _ = d + 1 := add_comm 1 d
  have hleft : d * (1 + w * (d + 1)) = d + w * (d + 1) := by
    calc d * (1 + w * (d + 1)) = d * 1 + d * (w * (d + 1)) := by rw [mul_add]
      _ = d + (d * w) * (d + 1) := by rw [mul_one, mul_assoc]
      _ = d + (w * d) * (d + 1) := by rw [hdw]
      _ = d + w * (d * (d + 1)) := by rw [mul_assoc]
      _ = d + w * (d + 1) := by rw [hde]
  have hτdτ : τ * d * τ = d := by
    calc τ * d * τ = d * τ * τ := by rw [← hdτ]
      _ = d * (τ * τ) := by rw [mul_assoc]
      _ = d := by rw [hτ, mul_one]
  have hτeτ : τ * (d + 1) * τ = d + 1 := by
    calc τ * (d + 1) * τ = τ * d * τ + τ * 1 * τ := by noncomm_ring
      _ = d + 1 := by rw [hτdτ, mul_one, hτ]
  have hright : τ * (1 + w * (d + 1)) * τ = d + w * (d + 1) := by
    calc τ * (1 + w * (d + 1)) * τ
        = τ * 1 * τ + (τ * w) * ((d + 1) * τ) := by noncomm_ring
      _ = 1 + ((w + 1) * τ) * ((d + 1) * τ) := by rw [mul_one, hτ, hτw']
      _ = 1 + (w + 1) * (τ * (d + 1) * τ) := by noncomm_ring
      _ = 1 + (w + 1) * (d + 1) := by rw [hτeτ]
      _ = 1 + (w * (d + 1) + 1 * (d + 1)) := by rw [add_mul]
      _ = 1 + (w * (d + 1) + (d + 1)) := by rw [one_mul]
      _ = d + w * (d + 1) := by
          have h1 : (1 : AddMonoid.End (VSub hD)) + 1 = 0 := VSub.add_self hD 1
          calc 1 + (w * (d + 1) + (d + 1)) = (1 + 1) + w * (d + 1) + d := by abel
            _ = 0 + w * (d + 1) + d := by rw [h1]
            _ = d + w * (d + 1) := by abel
  rw [hleft, hright]

theorem ThCyc.exists_mem_vConj_eq_one_add_w (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hτw : vConj hD t * w * vConj hD t = w + 1) {Q : Subgroup G}
    (hQ : QHyp L A D t Q) {g : G} (hgQ : g ∈ normalizer (Q : Set G))
    (hgw : vConj hD g * w = w * vConj hD g) {s₀ : G}
    (hs₀ : s₀ ∈ L ⊓ normalizer (A : Set G))
    (hs₀2 : ∀ a ∈ A, s₀ * (s₀ * a * s₀⁻¹) * s₀⁻¹ = a)
    (hu : ∀ v ∈ omega1 D hD.comm,
      (g⁻¹ * t * g) * v * (g⁻¹ * t * g)⁻¹ = (t * s₀) * v * (t * s₀)⁻¹) :
    ∃ x ∈ normalizer (Q : Set G) ⊓ wComm hD w,
      vConj hD x = 1 + w * (vConj hD s₀ + 1) := by
  classical
  let τ : AddMonoid.End (VSub hD) := vConj hD t
  let δ : AddMonoid.End (VSub hD) := vConj hD s₀
  let X : AddMonoid.End (VSub hD) := 1 + w * (δ + 1)
  let ρ : AddMonoid.End (VSub hD) := vConj hD g
  let ρi : AddMonoid.End (VSub hD) := vConj hD g⁻¹
  let Z : AddMonoid.End (VSub hD) := ρ * X
  have hAL : A ≤ L := fun a ha => W.S_le ((W.mem_A_iff a).1 ha).1
  have hAV : A ≤ omega1 D hD.comm := H.A_le_omega1 W W2 hD
  have hs₀V : s₀ ∈ normalizer (omega1 D hD.comm : Set G) :=
    ThCyc.vConj_mem_normalizer_omega1_of_mem_Hn H W W2 hD hs₀
  have htV : t ∈ normalizer (omega1 D hD.comm : Set G) :=
    H.t_mem_normalizer_omega1 W W2 hD
  have hgV : g ∈ normalizer (omega1 D hD.comm : Set G) :=
    QHyp.mem_normalizer_omega1 hD hQ hgQ
  have hg'V : g⁻¹ ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).inv_mem hgV
  have hτ : τ * τ = 1 := H.vConj_t_mul_self W W2 hD
  have hδw : δ * w = w * δ := hwH s₀ hs₀
  have hδτ : δ * τ = τ * δ :=
    ThCyc.vConj_comm_tau_of_mem_Hn H W W2 hD hs₀
  have hδδ : δ * δ = 1 :=
    ThCyc.vConj_mul_self_eq_one_of_sq_fixes H W W2 hD hwH hτw hs₀ hs₀2
  have hee : (δ + 1) * (δ + 1) = 0 := ThCyc.add_one_mul_add_one_eq_zero hD hδδ
  have hew : (δ + 1) * w = w * (δ + 1) := by
    rw [add_mul, one_mul, hδw, mul_add, mul_one]
  have hXX : X * X = 1 := by
    dsimp only [X]
    exact ThCyc.one_add_mul_mul_self hD hee hew
  have hτw' : τ * w = (w + 1) * τ := ThCyc.tau_mul_w H W W2 hD hτw
  have hδX : δ * X = τ * X * τ := by
    dsimp only [X]
    exact ThCyc.delta_mul_one_add_w_eq hD hτ hδτ hδw hτw' hδδ
  have hXw : X * w = w * X := by
    dsimp only [X]
    exact ThCyc.one_add_w_mul_comm hD hew
  have hgtgV : g⁻¹ * t * g ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).mul_mem
      ((normalizer (omega1 D hD.comm : Set G)).mul_mem hg'V htV) hgV
  have htsV : t * s₀ ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).mul_mem htV hs₀V
  have hρ : vConj hD (g⁻¹ * t * g) = vConj hD (t * s₀) := by
    apply AbelianSub.end_ext
    intro x
    rw [val_vConj_apply hD hgtgV, val_vConj_apply hD htsV]
    exact hu x.val (AbelianSub.val_mem x)
  have hleft : vConj hD (g⁻¹ * t * g) = ρi * τ * ρ := by
    rw [vConj_mul hD
        ((normalizer (omega1 D hD.comm : Set G)).mul_mem hg'V htV) hgV,
      vConj_mul hD hg'V htV]
  have hright : vConj hD (t * s₀) = τ * δ := vConj_mul hD htV hs₀V
  have hmain : ρi * τ * ρ = τ * δ := by
    rw [← hleft, hρ, hright]
  have hρτ : τ * ρ = ρ * (τ * δ) := by
    have h1 : ρ * ρi = 1 := vConj_mul_inv hD hgV
    have h2 : ρi * ρ = 1 := vConj_inv_mul hD hgV
    calc τ * ρ = (ρ * ρi) * τ * (ρ * ρi) * ρ := by rw [h1]; noncomm_ring
      _ = ρ * (ρi * τ * ρ) * ρi * ρ := by noncomm_ring
      _ = ρ * (τ * δ) * ρi * ρ := by rw [hmain]
      _ = ρ * (τ * δ) * (ρi * ρ) := by noncomm_ring
      _ = ρ * (τ * δ) := by rw [h2, mul_one]
  have hτZ : τ * Z = Z * τ := by
    dsimp only [Z]
    calc τ * (ρ * X) = (τ * ρ) * X := by noncomm_ring
      _ = (ρ * (τ * δ)) * X := by rw [hρτ]
      _ = ρ * (τ * (δ * X)) := by noncomm_ring
      _ = ρ * (τ * (τ * X * τ)) := by rw [hδX]
      _ = ρ * ((τ * τ) * (X * τ)) := by rfl
      _ = (ρ * X) * τ := by rw [hτ]; noncomm_ring
  have hZw : Z * w = w * Z := by
    dsimp only [Z]
    calc (ρ * X) * w = ρ * (X * w) := by noncomm_ring
      _ = ρ * (w * X) := by rw [hXw]
      _ = (ρ * w) * X := by noncomm_ring
      _ = (w * ρ) * X := by rw [hgw]
      _ = w * (ρ * X) := by noncomm_ring
  have hZA : ∀ x : VSub hD, x.val ∈ A → (Z x).val ∈ A := by
    intro x hx
    have hfix : τ (Z x) = Z x := by
      have h := congrArg (fun e : AddMonoid.End (VSub hD) => e x) hτZ
      have h' : τ (Z x) = Z (τ x) := by
        simpa only [AddMonoid.End.coe_mul, Function.comp_apply] using h
      rwa [show τ x = x from ThCyc.tau_apply_of_mem_A H W W2 hD hx] at h'
    have hval : t * (Z x).val * t⁻¹ = (Z x).val := by
      have h := congrArg AbelianSub.val hfix
      rwa [val_vConj_apply hD htV] at h
    have hcomm : (Z x).val * t = t * (Z x).val := by
      calc (Z x).val * t = (t * (Z x).val * t⁻¹) * t := by rw [hval]
        _ = t * (Z x).val := by group
    have hmem : (Z x).val ∈ omega1 D hD.comm ⊓ centralizer ({t} : Set G) :=
      ⟨AbelianSub.val_mem _, mem_centralizer_singleton_iff.2 hcomm⟩
    rwa [H.omega1_inf_centralizer_t W W2 hD] at hmem
  have hZinj : Function.Injective Z := by
    intro x y hxy
    have h1 : X x = X y := by
      have h := congrArg ρi hxy
      have h' : (ρi * ρ) (X x) = (ρi * ρ) (X y) := h
      rw [vConj_inv_mul hD hgV] at h'
      simpa using h'
    have h2 := congrArg X h1
    have h3 : (X * X) x = (X * X) y := h2
    rw [hXX] at h3
    simpa using h3
  let f : G → G := fun a => if ha : a ∈ A then (Z (AbelianSub.mk a (hAV ha))).val else 1
  have hfdef : ∀ (a : G) (ha : a ∈ A),
      f a = (Z (AbelianSub.mk a (hAV ha))).val := by
    intro a ha
    dsimp only [f]
    rw [dif_pos ha]
  have hfA : ∀ a ∈ A, f a ∈ A := by
    intro a ha
    rw [hfdef a ha]
    exact hZA _ (by simpa using ha)
  have hfmul : ∀ a ∈ A, ∀ a' ∈ A, f (a * a') = f a * f a' := by
    intro a ha a' ha'
    rw [hfdef (a * a') (A.mul_mem ha ha'), hfdef a ha, hfdef a' ha']
    have hmul : (AbelianSub.mk (a * a') (hAV (A.mul_mem ha ha')) : VSub hD) =
        AbelianSub.mk a (hAV ha) + AbelianSub.mk a' (hAV ha') :=
      AbelianSub.mk_mul a a' (hAV ha) (hAV ha')
    rw [hmul, map_add, AbelianSub.val_add]
  have hfinj : ∀ a ∈ A, ∀ a' ∈ A, f a = f a' → a = a' := by
    intro a ha a' ha' hab
    rw [hfdef a ha, hfdef a' ha'] at hab
    have hZ : Z (AbelianSub.mk a (hAV ha)) = Z (AbelianSub.mk a' (hAV ha')) :=
      AbelianSub.ext hab
    exact congrArg AbelianSub.val (hZinj hZ)
  obtain ⟨h₀, hh₀L, hh₀conj⟩ := W.surj f hfA hfmul hfinj
  have hh₀A : ∀ a ∈ A, h₀ * a * h₀⁻¹ ∈ A := by
    intro a ha
    rw [hh₀conj a ha, hfdef a ha]
    exact hZA _ (by simpa using ha)
  have hh₀N : h₀ ∈ normalizer (A : Set G) := by
    have hmaple : A.map (MulAut.conj h₀).toMonoidHom ≤ A := by
      rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hh₀A a ha
    have hcard : Nat.card (A.map (MulAut.conj h₀).toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective (f := (MulAut.conj h₀).toMonoidHom)
        (MulAut.conj h₀).injective
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2
      (Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm))
  have hh₀V : h₀ ∈ normalizer (omega1 D hD.comm : Set G) :=
    ThCyc.vConj_mem_normalizer_omega1_of_mem_Hn H W W2 hD ⟨hh₀L, hh₀N⟩
  have hh₀w : vConj hD h₀ * w = w * vConj hD h₀ := hwH h₀ ⟨hh₀L, hh₀N⟩
  have hAZ : ∀ x : VSub hD, x.val ∈ A → vConj hD h₀ x = Z x := by
    intro x hx
    have hxmk : x = AbelianSub.mk x.val (hAV hx) := (AbelianSub.mk_val x).symm
    rw [hxmk]
    apply AbelianSub.ext
    rw [val_vConj_apply hD hh₀V, AbelianSub.val_mk, hh₀conj x.val hx]
    exact hfdef x.val hx
  have hh₀Z : vConj hD h₀ = Z :=
    H.end_eq_of_commute_of_eq_on_A W W2 hD hτw hh₀w hZw hAZ
  have hh₀Q : h₀ ∈ normalizer (Q : Set G) :=
    le_normalizer_of_conj_mem (N := L ⊓ normalizer (A : Set G)) (D := Q)
      (fun n hn => hQ.conj_mem n hn) ⟨hh₀L, hh₀N⟩
  refine ⟨g⁻¹ * h₀, ⟨(normalizer (Q : Set G)).mul_mem
    ((normalizer (Q : Set G)).inv_mem hgQ) hh₀Q, ?_⟩, ?_⟩
  ·
    have hxV : g⁻¹ * h₀ ∈ normalizer (omega1 D hD.comm : Set G) :=
      (normalizer (omega1 D hD.comm : Set G)).mul_mem hg'V hh₀V
    have hxconj : vConj hD (g⁻¹ * h₀) = X := by
      rw [vConj_mul hD hg'V hh₀V, hh₀Z]
      change ρi * (ρ * X) = X
      rw [← mul_assoc, vConj_inv_mul hD hgV, one_mul]
    refine ⟨hxV, ?_⟩
    rw [hxconj]
    exact hXw
  · rw [vConj_mul hD hg'V hh₀V, hh₀Z]
    change ρi * (ρ * X) = 1 + w * (vConj hD s₀ + 1)
    rw [← mul_assoc, vConj_inv_mul hD hgV, one_mul]

end CFSG.EvenSporadicStandard.ThStd
