module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsZ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Inputs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121A
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Yc
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Pow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Inv
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4D
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Proj
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4U
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Fus
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Cent

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec124_tu_not_mem [Finite G] {t : G} {L S E : Subgroup G} (F : Sec12Frame t L S)
    (hE : IsSylow2Of E (secCMB t S L)) {u : G} {φ : (Fin 5 → ZMod 2) → G}
    (hφB : ∀ v, IsEvenVec v → φ v ∈ secB S L)
    (hφinj : ∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → v = w)
    (huφ : ∀ v, IsEvenVec v → u * φ v * u⁻¹ = φ (permVec sec124Sigma v)) :
    t * u ∉ secV t S L E := by
  intro hmem
  obtain ⟨n₁, n₂, hn₁, hn₂, -, -, -, hσ⟩ := sec124_vectors
  have hcent : (t * u) ∈ centralizer (secB S L : Set G) :=
    (Subgroup.mem_inf.mp (hE.1 (sec121_V_le_E F hE hmem))).2
  have hb : φ n₁ ∈ secB S L := hφB n₁ hn₁
  have hb' : φ (permVec sec124Sigma n₁) ∈ secB S L := hφB _ (isEvenVec_permVec _ hn₁)
  have h2 : (t * u) * φ n₁ * (t * u)⁻¹ = φ n₁ := by
    have h := (Subgroup.mem_centralizer_iff.mp hcent) (φ n₁) hb
    calc (t * u) * φ n₁ * (t * u)⁻¹ = (φ n₁ * (t * u)) * (t * u)⁻¹ := by rw [h]
      _ = φ n₁ := by group
  have h3 : (t * u) * φ n₁ * (t * u)⁻¹ = φ (permVec sec124Sigma n₁) := by
    calc (t * u) * φ n₁ * (t * u)⁻¹ = t * (u * φ n₁ * u⁻¹) * t⁻¹ := by group
      _ = t * φ (permVec sec124Sigma n₁) * t⁻¹ := by rw [huφ n₁ hn₁]
      _ = φ (permVec sec124Sigma n₁) := by rw [sec12E_t_comm_B F hb']; group
  exact hσ (hφinj _ _ (isEvenVec_permVec _ hn₁) hn₁ (h3.symm.trans h2))

theorem asc82StepNoZ4_of_out (hp : Asc82Pre11) (hSp : Asc82FactSplit5)
    (hOut : Asc82StepZ4Out) : Asc82StepNoZ4 := by
  intro G _ _ t L S z K1 K2 E hctx hZ
  have F : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  obtain ⟨hPSp, -, htL, htS, -, hSyl⟩ := hp.basic G t L S z hctx.toSec10Ctx.toSec10Z
  have hS : IsSylow2Of S (centralizer ({t} : Set G)) := hctx.sylow
  have hE : IsSylow2Of E (secCMB t S L) := hctx.sylowE
  obtain ⟨φ, hφ, -⟩ := F.bdata.2.2.2.2.2
  have hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)) := by
    rw [F.bdata.2.2.2.2.1]
    exact hφ
  have hφB : ∀ v, IsEvenVec v → φ v ∈ secB S L := fun v hv =>
    (hperm.2.2.1 (φ v)).mpr ⟨v, hv, rfl⟩
  have hBV : secB S L ≤ secV t S L E := sec121_B_le_V F hE
  have hB2 : ∀ b ∈ secB S L, b * b = 1 := fun b hb => sec12E_B_sq F hb
  have hVab := sec124_z4_comm hZ
  have htinv := sec124_t_inv F hE hZ
  obtain ⟨X0, hX0B, hX0sup⟩ := hSp G t L S z K1 K2 hctx.toSec10Ctx hPSp
    (sec122_S_le_normalizer_L F hS.1) (sec122_centralizer_inf_S F hS htS) hSyl htL
  obtain ⟨u, huY, hu2, huφ⟩ := sec124_exists_u F hX0B hX0sup hperm
  have huV : ∀ v ∈ secV t S L E, u * v * u⁻¹ ∈ secV t S L E := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (sec121_Y_le_normalizer_V F hE huY) v).mp hv
  obtain ⟨D, hDV, hD16, hDs, w, hwD, hw2⟩ := sec124_Dsub hVab hB2
    (sec124_z4_root hZ hBV hB2) hperm.1 hφB hperm.2.1 huV hu2 huφ htinv
  obtain ⟨l, hl, b, hb, hlb⟩ := hp.facts.invB G L hPSp (S ⊓ L) hSyl u huY.2 hu2
  obtain ⟨h, hh⟩ := sec124_fusion F hl hb hlb
  let D' : Subgroup G := D.map (MulAut.conj h).toMonoidHom
  have hD'mem : ∀ x, x ∈ D' ↔ ∃ d ∈ D, h * d * h⁻¹ = x := by
    intro x
    simp [D', Subgroup.mem_map, MulAut.conj_apply]
  have hD'card : Nat.card D' = 16 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hD16]
  have hD'ab : ∀ a ∈ D', ∀ b ∈ D', a * b = b * a := by
    intro a ha b hb
    obtain ⟨d, hd, rfl⟩ := (hD'mem a).mp ha
    obtain ⟨d', hd', rfl⟩ := (hD'mem b).mp hb
    have hcomm := hVab d (hDV hd) d' (hDV hd')
    calc h * d * h⁻¹ * (h * d' * h⁻¹) = h * (d * d') * h⁻¹ := by group
      _ = h * (d' * d) * h⁻¹ := by rw [hcomm]
      _ = h * d' * h⁻¹ * (h * d * h⁻¹) := by group
  have hD'cent : ∀ x ∈ D', t * x * t⁻¹ = x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := (hD'mem x).mp hx
    calc t * (h * d * h⁻¹) * t⁻¹
        = h * ((h⁻¹ * t * h) * d * (h⁻¹ * t * h)⁻¹) * h⁻¹ := by group
      _ = h * ((t * u) * d * (t * u)⁻¹) * h⁻¹ := by rw [hh]
      _ = h * d * h⁻¹ := by rw [hDs d hd]
  have hD'Ct : ∀ x ∈ D', x ∈ centralizer ({t} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyt : y = t := by simpa using hy
    rw [hyt]
    calc t * x = (t * x * t⁻¹) * t := by group
      _ = x * t := by rw [hD'cent x hx]
  have hSK : S ≤ L ⊔ centralizer (L : Set G) := hOut G t L S z K1 K2 E hctx hZ
  have hCK : centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G) :=
    sec124_cent_le_K (hp.facts.out5 G L hPSp) F.hCt hS hSK
  have hD'K : D' ≤ L ⊔ centralizer (L : Set G) := fun x hx => hCK (hD'Ct x hx)
  have hD'C : D' ⊓ centralizer (L : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxD', hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨d, hd, rfl⟩ := (hD'mem x).mp hxD'
    have hx2 : ∃ k : ℕ, (h * d * h⁻¹) ^ (2 ^ k) = 1 := by
      refine ⟨2, ?_⟩
      have h4 : d ^ 4 = 1 := sec124_z4_pow_four hZ d (hDV hd)
      calc (h * d * h⁻¹) ^ (2 ^ 2) = h * d ^ 4 * h⁻¹ := by rw [conj_pow]; norm_num
        _ = 1 := by rw [h4]; group
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (F.two _ hxC (hD'Ct _ hxD') hx2)
    have hmod : t ^ (i % ((orderOf t : ℕ) : ℤ)) = t ^ i := zpow_mod_orderOf t i
    rw [F.ht2] at hmod
    have hk : i % ((2 : ℕ) : ℤ) = 0 ∨ i % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases hk with hk | hk
    · rw [hk, zpow_zero] at hmod
      rw [← hi, ← hmod]
    · exfalso
      rw [hk, zpow_one] at hmod
      have hdt : h * d * h⁻¹ = t := by rw [← hi, ← hmod]
      have hd_eq : d = t * u := by
        have h1 : d = h⁻¹ * (h * d * h⁻¹) * h := by group
        rw [h1, hdt, hh]
      exact sec124_tu_not_mem F hE hφB hperm.2.1 huφ (hd_eq ▸ hDV hd)
  have hwD' : h * w * h⁻¹ ∈ D' := (hD'mem _).mpr ⟨w, hwD, rfl⟩
  have hw2' : (h * w * h⁻¹) * (h * w * h⁻¹) ≠ 1 := by
    intro h1
    apply hw2
    have h2 : h * (w * w) * h⁻¹ = 1 := by rw [← h1]; group
    have h3 : w * w = h⁻¹ * (h * (w * w) * h⁻¹) * h := by group
    rw [h3, h2]
    group
  exact sec124_absurd hp.facts.b5 hPSp F.hLC hD'K hD'C hD'ab hD'card hwD' hw2'

end CFSG.OddStandard.SmallF3.Omega
