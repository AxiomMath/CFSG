module

public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.QuasithinUnique.Bridge.Alt57Model

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall

variable {K : Type} [Field K] [CharP K 2]

theorem cayleyMul_eq_zornMul (x y : quasithinZorn K) : cayleyMul x y = quasithinZornMul x y := by
  obtain ⟨r, u, v, s⟩ := x
  obtain ⟨t, a, b, z⟩ := y
  simp only [cayleyMul, quasithinZornMul]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [CharTwo.sub_eq_add]
  · funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem zornMul_self_eq (x : quasithinZorn K) :
    quasithinZornMul x x = cayleyTr x • x + cayleyNorm x • (zornOne : quasithinZorn K) := by
  rw [zornMul_self]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨r, u, v, s⟩ := x
  simp only [cayleyTr, cayleyNorm, zornOne, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero,
    smul_eq_mul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only
    linear_combination (-(r * s)) * h2
  · simp only
  · simp only
  · simp only
    have hvu : ∑ i, v i * u i = ∑ i, u i * v i := Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hvu]
    linear_combination (-(r * s)) * h2

theorem isZornAuto_tr_norm {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : IsZornAuto g)
    (x : quasithinZorn K) : cayleyTr (g x) = cayleyTr x ∧ cayleyNorm (g x) = cayleyNorm x := by
  have hone : g zornOne = zornOne := hg.map_one
  have h1 : quasithinZornMul (g x) (g x) =
      cayleyTr x • g x + cayleyNorm x • (zornOne : quasithinZorn K) := by
    rw [← hg x x, zornMul_self_eq x, map_add, map_smul, map_smul, hone]
  have h2 := zornMul_self_eq (g x)
  have hE := h1.symm.trans h2
  have hf := congrArg Prod.fst hE
  have h4 := congrArg (fun z : quasithinZorn K => z.2.2.2) hE
  have hu : ∀ i, cayleyTr x * (g x).2.1 i = cayleyTr (g x) * (g x).2.1 i := fun i => by
    have := congrFun (congrArg (fun z : quasithinZorn K => z.2.1) hE) i
    simpa [zornOne] using this
  have hv : ∀ i, cayleyTr x * (g x).2.2.1 i = cayleyTr (g x) * (g x).2.2.1 i := fun i => by
    have := congrFun (congrArg (fun z : quasithinZorn K => z.2.2.1) hE) i
    simpa [zornOne] using this
  simp only [zornOne, Prod.smul_fst, Prod.fst_add, Prod.smul_snd, Prod.snd_add, smul_eq_mul,
    mul_one] at hf h4
  by_cases htt : cayleyTr x = cayleyTr (g x)
  · refine ⟨htt.symm, ?_⟩
    rw [htt] at hf
    exact (add_left_cancel hf).symm
  · exfalso
    have hne : cayleyTr x - cayleyTr (g x) ≠ 0 := sub_ne_zero.2 htt
    have hu0 : (g x).2.1 = 0 := funext fun i => by
      have h : (cayleyTr x - cayleyTr (g x)) * (g x).2.1 i = 0 := by rw [sub_mul, hu i, sub_self]
      exact (mul_eq_zero.1 h).resolve_left hne
    have hv0 : (g x).2.2.1 = 0 := funext fun i => by
      have h : (cayleyTr x - cayleyTr (g x)) * (g x).2.2.1 i = 0 := by rw [sub_mul, hv i, sub_self]
      exact (mul_eq_zero.1 h).resolve_left hne
    have hc : (g x).1 = (g x).2.2.2 := by
      have h : (cayleyTr x - cayleyTr (g x)) * ((g x).1 - (g x).2.2.2) = 0 := by
        linear_combination hf - h4
      have := (mul_eq_zero.1 h).resolve_left hne
      exact sub_eq_zero.1 this
    have hgx : g x = ((g x).1, 0, 0, (g x).1) := by
      refine Prod.ext rfl (Prod.ext hu0 (Prod.ext hv0 hc.symm))
    have hx : x = ((g x).1, 0, 0, (g x).1) := by
      apply g.injective
      rw [hg.map_smul_one, ← hgx]
    have htx : cayleyTr x = 0 := by
      rw [hx]
      exact CharTwo.add_self_eq_zero _
    have hty : cayleyTr (g x) = 0 := by
      rw [hgx]
      exact CharTwo.add_self_eq_zero _
    exact htt (htx.trans hty.symm)

theorem quasithinG2_eq_cayleyGroup : quasithinG2 K = cayleyGroup K := by
  apply le_antisymm
  · intro g hg
    have hz := mem_quasithinG2_isZornAuto hg
    refine ⟨hz.map_one, fun x y => ?_, fun x => (isZornAuto_tr_norm hz x).1,
      fun x => (isZornAuto_tr_norm hz x).2⟩
    rw [cayleyMul_eq_zornMul, cayleyMul_eq_zornMul]
    exact hz x y
  · intro g hg
    apply Subgroup.subset_closure
    intro x y
    rw [← cayleyMul_eq_zornMul, ← cayleyMul_eq_zornMul]
    exact hg.2.1 x y

end CFSG.QuasithinUnique.Bridge.Alt57Model
