module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinTorus
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinCuts

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher (flagStabilizer)

variable {K : Type} [Field K]

theorem exists_sl_conj_eq_of_card_four [Finite K] (hK : Nat.card K = 4) {m : ℕ} (hm : m = 2)
    (g : GL (Fin m) K) :
    ∃ s ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range,
      ∀ u : GL (Fin m) K, g * u * g⁻¹ = s * u * s⁻¹ := by
  subst hm
  set c : Kˣ := GeneralLinearGroup.det g with hc
  have hc3 : c ^ 3 = 1 := by
    have h3 : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
    rw [← h3]
    exact pow_card_eq_one'
  have hdet : ((GeneralLinearGroup.scalar (Fin 2) c * g : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Units.val_mul, det_mul, GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← GeneralLinearGroup.val_det_apply,
      ← hc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ, hc3, Units.val_one]
  have hcen : ∀ x : GL (Fin 2) K, GeneralLinearGroup.scalar (Fin 2) c * x =
      x * GeneralLinearGroup.scalar (Fin 2) c := fun x => Units.ext <| by
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute (c : K) (fun r' => Commute.all _ _) _).eq
  refine ⟨GeneralLinearGroup.scalar (Fin 2) c * g, ⟨⟨_, hdet⟩, Units.ext rfl⟩, fun u => ?_⟩
  calc g * u * g⁻¹ = g * u * g⁻¹ * (GeneralLinearGroup.scalar (Fin 2) c *
        (GeneralLinearGroup.scalar (Fin 2) c)⁻¹) := by group
    _ = GeneralLinearGroup.scalar (Fin 2) c * (g * u * g⁻¹) *
        (GeneralLinearGroup.scalar (Fin 2) c)⁻¹ := by rw [hcen (g * u * g⁻¹)]; group
    _ = GeneralLinearGroup.scalar (Fin 2) c * g * u *
        (GeneralLinearGroup.scalar (Fin 2) c * g)⁻¹ := by group

theorem linLeviHom_inner_of_sixty [Finite K] (hK : Nat.card K = 4) {n : ℕ} {I : Set ℕ}
    (a : Fin n) (hq : CFSG.Open.IsQuasisimple ↥(linBlockSL K n I a))
    (h60 : Nat.card (↥(linBlockSL K n I a) ⧸ Subgroup.center ↥(linBlockSL K n I a)) = 60)
    (q : LinearFlag.flagStabilizer n K I) :
    ∃ s ∈ linBlockSL K n I a, ∀ u ∈ linBlockSL K n I a,
      linLeviHom K n I q a * u * (linLeviHom K n I q a)⁻¹ = s * u * s⁻¹ := by
  obtain ⟨hm, -⟩ := linBlock_eq_two_of_sixty (f := 2) (by rw [hK]; norm_num) hq h60
  obtain ⟨s, hs, hsu⟩ := exists_sl_conj_eq_of_card_four hK hm (linLeviHom K n I q a)
  exact ⟨s, hs, fun u _ => hsu u⟩

theorem spFlagLeviHom_inner_of_sixty [Finite K] [CharP K 2] (hK : Nat.card K = 4) {r : ℕ}
    {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ r) {t : ℕ} (htI : t ∈ I) (j : Fin (r + 1))
    (hq : CFSG.Open.IsQuasisimple ↥(spFlagLeviBlock (K := K) hI t j))
    (h60 : Nat.card (↥(spFlagLeviBlock (K := K) hI t j) ⧸
      Subgroup.center ↥(spFlagLeviBlock (K := K) hI t j)) = 60)
    (q : flagStabilizer r K I) :
    ∃ s ∈ spFlagLeviBlock (K := K) hI t j, ∀ u ∈ spFlagLeviBlock (K := K) hI t j,
      spFlagLeviHom hI htI q j * u * (spFlagLeviHom hI htI q j)⁻¹ = s * u * s⁻¹ := by
  have hcoord : spFlagLeviHom hI htI q j = spFlagLeviCoord hI htI j q := rfl
  rcases (spFlagLeviBlock_sixty hI t hq h60).2.2 with ⟨hj0, hrt⟩ | ⟨hj0, hjI, hlen⟩
  ·
    refine ⟨spFlagLeviHom hI htI q j, ?_, fun u _ => rfl⟩
    have hperf := (spFlag_isQuasisimple_Sp (K := K) (m := r - t) (by omega)
      (Or.inl (by rw [hK]))).1
    rw [spFlagLeviBlock_of_eq_zero hI hj0, hcoord, spFlagLeviCoord_of_eq_zero hI htI hj0,
      MonoidHom.comp_apply]
    exact Subgroup.mem_map_of_mem _ (hperf ▸ Subgroup.mem_top _)
  ·
    rw [hcoord, spFlagLeviCoord_of_mem hI htI hj0 hjI, MonoidHom.comp_apply]
    rw [spFlagLeviBlock_of_mem hI hj0 hjI]
    obtain ⟨s₀, ⟨s₁, rfl⟩, hs₀⟩ :=
      exists_sl_conj_eq_of_card_four hK hlen (spFlagCutHom hI (spFlagPrev_mem I j) hjI q)
    refine ⟨spFlagCutEmb (spFlagPrev I j) j (hI j hjI) (SpecialLinearGroup.toGL s₁),
      ⟨s₁, rfl⟩, ?_⟩
    rintro _ ⟨u₁, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul, hs₀, map_mul, map_mul, map_inv]
