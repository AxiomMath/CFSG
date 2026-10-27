module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNBase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMA6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMAut
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L66In
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B : Subgroup G}

private theorem sec9m_conj_centralizer {H : Subgroup G} {s c : G}
    (hs : s ∈ normalizer (H : Set G)) (hc : c ∈ centralizer (H : Set G)) :
    s * c * s⁻¹ ∈ centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro l hl
  have hl' : s⁻¹ * l * s ∈ H := (Subgroup.mem_normalizer_iff''.mp hs l).mp hl
  calc l * (s * c * s⁻¹) = s * ((s⁻¹ * l * s) * c) * s⁻¹ := by group
    _ = s * (c * (s⁻¹ * l * s)) * s⁻¹ := by rw [hc (s⁻¹ * l * s) hl']
    _ = (s * c * s⁻¹) * l := by group

theorem sec9m_conj_t0 (hT : Asc82Tab9M) (hctx : Sec9Ctx G t L S z g B t₀) {x : G}
    (hxL : x ∈ L) (hxB : x ∈ normalizer (B : Set G)) :
    ∃ b ∈ B, ∃ d ∈ L ⊓ centralizer (L : Set G), x * t₀ * x⁻¹ = b * d * t₀ := by
  have hLM : IsOm6M L := ⟨hctx.toSec3SettingLB.component.isQuasisimple, hctx.omega6m⟩
  have ht0N : t₀ ∈ normalizer (L : Set G) := sec9n_t0_mem_normalizer hctx
  have hxN : x ∈ normalizer (L : Set G) := Subgroup.le_normalizer hxL
  have hx'N : x * t₀ * x⁻¹ ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem
      ((normalizer (L : Set G)).mul_mem hxN ht0N)
      ((normalizer (L : Set G)).inv_mem hxN)
  have hx'B : ∀ b ∈ B, (x * t₀ * x⁻¹) * b = b * (x * t₀ * x⁻¹) := by
    intro b hb
    have hxb : x⁻¹ * b * x ∈ B := (Subgroup.mem_normalizer_iff''.mp hxB b).mp hb
    have hfix : (x * t₀ * x⁻¹) * b * (x * t₀ * x⁻¹)⁻¹ = b := by
      rw [show (x * t₀ * x⁻¹) * b * (x * t₀ * x⁻¹)⁻¹ =
        x * (t₀ * (x⁻¹ * b * x) * t₀⁻¹) * x⁻¹ by group,
        hctx.t0_B (x⁻¹ * b * x) hxb]
      group
    calc (x * t₀ * x⁻¹) * b
        = ((x * t₀ * x⁻¹) * b * (x * t₀ * x⁻¹)⁻¹) * (x * t₀ * x⁻¹) := by group
      _ = b * (x * t₀ * x⁻¹) := by rw [hfix]
  have hBL : B ≤ L := fun b hb => (hctx.B_le hb).1
  obtain ⟨P0, hP0, hBP0⟩ := sec68_exists_sylow_ge (H := L) hctx.B_e16.1.isPGroup hBL
  obtain ⟨b₁, hb₁, c, hc, hbc⟩ :=
    hT.cent_B_i3 G L hLM P0 hP0 B hBP0 hctx.B_e16 t₀ ht0N hctx.t0_B
      (hT.i3_outer G L hLM t₀ ht0N hctx.t0_type) (x * t₀ * x⁻¹) hx'N hx'B
  rcases hbc with hbc | hbc
  · exfalso
    have hcx : Commute x c := Subgroup.mem_centralizer_iff.mp hc x hxL
    have hcx' : x⁻¹ * c * x = c := hcx.inv_mul_cancel
    have hxbin : x⁻¹ * b₁ * x ∈ L :=
      L.mul_mem (L.mul_mem (L.inv_mem hxL) (hBL hb₁)) hxL
    have hthis : t₀ = (x⁻¹ * b₁ * x) * c := by
      calc t₀ = x⁻¹ * (x * t₀ * x⁻¹) * x := by group
        _ = x⁻¹ * (b₁ * c) * x := by rw [hbc]
        _ = (x⁻¹ * b₁ * x) * c := by
              rw [show x⁻¹ * (b₁ * c) * x = (x⁻¹ * b₁ * x) * (x⁻¹ * c * x) by group,
                hcx']
    exact (hT.i3_outer G L hLM t₀ ht0N hctx.t0_type) (by
      change t₀ ∈ L ⊔ centralizer (L : Set G)
      rw [hthis]
      exact Subgroup.mul_mem_sup hxbin hc)
  · refine ⟨b₁, hb₁, t₀ * c * t₀⁻¹, ⟨?_, ?_⟩, ?_⟩
    · have ht0c : t₀ * c = b₁⁻¹ * (x * t₀ * x⁻¹) := by
        rw [show x * t₀ * x⁻¹ = b₁ * t₀ * c from hbc]
        group
      have hxinvL : t₀ * x⁻¹ * t₀⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp ht0N x⁻¹).mp (L.inv_mem hxL)
      have hd_eq : t₀ * c * t₀⁻¹ = (b₁⁻¹ * x) * (t₀ * x⁻¹ * t₀⁻¹) := by
        rw [ht0c]; group
      rw [hd_eq]
      exact L.mul_mem (L.mul_mem (L.inv_mem (hBL hb₁)) hxL) hxinvL
    · exact sec9m_conj_centralizer ht0N hc
    · rw [hbc]; group

theorem sec9m_commutator_mem_B (hctx : Sec9Ctx G t L S z g B t₀) {x : G}
    (hxL : x ∈ L) (hxB : x ∈ normalizer (B : Set G))
    (ht0mem : x * t₀ * x⁻¹ * t₀⁻¹ ∈ B) :
    ∀ a ∈ Asub9 t t₀ B, x * a * x⁻¹ * a⁻¹ ∈ B := by
  have hxt : Commute x t := Subgroup.mem_centralizer_iff.mp (sec9n_t_mem_cent hctx) x hxL
  have hxt1 : ⁅x, t⁆ = 1 := hxt.commutator_eq
  have hxBn : ∀ c ∈ B, x * c * x⁻¹ ∈ B := fun c hc =>
    (Subgroup.mem_normalizer_iff.mp hxB c).mp hc
  have hcommB : ∀ c ∈ B, ⁅x, c⁆ ∈ B := by
    intro c hc
    rw [commutatorElement_def]
    exact B.mul_mem (hxBn c hc) (B.inv_mem hc)
  have htB : ∀ c ∈ B, t * c * t⁻¹ = c := by
    intro c hc
    rw [sec9n_t_B hctx c hc]; group
  have ht0B : ∀ c ∈ B, t₀ * c * t₀⁻¹ = c := by
    intro c hc
    rw [hctx.t0_B c hc]; group
  have hcommt0 : ⁅x, t₀⁆ ∈ B := by
    rw [commutatorElement_def]; exact ht0mem
  have hcommt0b : ∀ c ∈ B, ⁅x, t₀ * c⁆ ∈ B := by
    intro c hc
    rw [commutatorElement_mul_right_eq_mul_conj,
      show ⁅x, t₀⁆ * t₀ * ⁅x, c⁆ * t₀⁻¹ = ⁅x, t₀⁆ * (t₀ * ⁅x, c⁆ * t₀⁻¹) by group,
      ht0B _ (hcommB c hc)]
    exact B.mul_mem hcommt0 (hcommB c hc)
  have hcommtb : ∀ c ∈ B, ⁅x, t * c⁆ ∈ B := by
    intro c hc
    rw [commutatorElement_mul_right_eq_mul_conj, hxt1, one_mul, htB _ (hcommB c hc)]
    exact hcommB c hc
  intro a ha
  obtain ⟨b, hb, h | h | h | h⟩ := sec9n_mem_A hctx ha
  · rw [h]; rw [← commutatorElement_def]; exact hcommB b hb
  · rw [h]; rw [← commutatorElement_def]; exact hcommtb b hb
  · rw [h]; rw [← commutatorElement_def]; exact hcommt0b b hb
  · rw [h, ← commutatorElement_def]
    rw [commutatorElement_mul_right_eq_mul_conj, hxt1, one_mul, htB _ (hcommt0b b hb)]
    exact hcommt0b b hb

theorem sec9m_lift (hT : Asc82Tab9M) (hctx : Sec9Ctx G t L S z g B t₀) {x : G}
    (hxL : x ∈ L) (hxB : x ∈ normalizer (B : Set G)) {j : ℕ} (hx : x ^ (2 ^ j) = 1) :
    x ∈ centMod (Asub9 t t₀ B) B := by
  obtain ⟨b, hb, d, hd, hconj⟩ := sec9m_conj_t0 hT hctx hxL hxB
  have hLM : IsOm6M L := ⟨hctx.toSec3SettingLB.component.isQuasisimple, hctx.omega6m⟩
  have hxb : ∀ c ∈ B, x * c * x⁻¹ ∈ B := fun c hc =>
    (Subgroup.mem_normalizer_iff.mp hxB c).mp hc
  have hdb : Commute d b :=
    (Subgroup.mem_centralizer_iff.mp hd.2 b (hctx.B_le hb).1).symm
  have hstep : ∀ k : ℕ, ∃ b_k ∈ B, x ^ k * t₀ * (x ^ k)⁻¹ = b_k * d ^ k * t₀ := by
    intro k
    induction k with
    | zero => exact ⟨1, B.one_mem, by simp⟩
    | succ k ih =>
        obtain ⟨bk, hbk, hbk_eq⟩ := ih
        refine ⟨(x * bk * x⁻¹) * b, ?_, ?_⟩
        · exact B.mul_mem (hxb bk hbk) hb
        · have hxd : x * d ^ k * x⁻¹ = d ^ k := by
            have hcx : Commute x d := Subgroup.mem_centralizer_iff.mp hd.2 x hxL
            rw [(hcx.pow_right k).eq]
            group
          have hdbk : d ^ k * b = b * d ^ k := (hdb.pow_left k).eq
          calc x ^ (k + 1) * t₀ * (x ^ (k + 1))⁻¹
              = x * (x ^ k * t₀ * (x ^ k)⁻¹) * x⁻¹ := by rw [pow_succ']; group
            _ = x * (bk * d ^ k * t₀) * x⁻¹ := by rw [hbk_eq]
            _ = (x * bk * x⁻¹) * d ^ k * (b * d * t₀) := by
                  rw [show x * (bk * d ^ k * t₀) * x⁻¹ =
                    (x * bk * x⁻¹) * (x * d ^ k * x⁻¹) * (x * t₀ * x⁻¹) by group,
                    hxd, hconj]
            _ = ((x * bk * x⁻¹) * b) * d ^ (k + 1) * t₀ := by
                  rw [show (x * bk * x⁻¹) * d ^ k * (b * d * t₀) =
                        (x * bk * x⁻¹) * (d ^ k * b) * d * t₀ by group, hdbk,
                    show (x * bk * x⁻¹) * (b * d ^ k) * d * t₀ =
                        ((x * bk * x⁻¹) * b) * (d ^ k * d) * t₀ by group,
                    ← pow_succ]
  obtain ⟨bk, hbk, hbk_eq⟩ := hstep (2 ^ j)
  have hbk_eq' : t₀ = bk * d ^ (2 ^ j) * t₀ := by
    rw [← hbk_eq, hx]; group
  have hd2j_eq : d ^ (2 ^ j) = bk⁻¹ := by
    have h2 : bk * d ^ (2 ^ j) = 1 := by
      calc bk * d ^ (2 ^ j) = bk * d ^ (2 ^ j) * t₀ * t₀⁻¹ := by group
        _ = t₀ * t₀⁻¹ := by rw [← hbk_eq']
        _ = 1 := by group
    exact mul_eq_one_iff_eq_inv'.mp h2
  have hd2j_one : d ^ (2 ^ j) = 1 :=
    sec9n_B_inf_cent hctx _ (by rw [hd2j_eq]; exact B.inv_mem hbk)
      ((centralizer (L : Set G)).pow_mem hd.2 _)
  have hdvd : orderOf d ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hd2j_one
  have hodd : Odd (orderOf d) := sec66_odd_of_mem_inf hLM hd
  have hd1 : d = 1 := by
    have hcop : Nat.Coprime (orderOf d) (2 ^ j) := (Nat.coprime_two_right.mpr hodd).pow_right j
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd)
  have ht0mem : x * t₀ * x⁻¹ * t₀⁻¹ ∈ B := by
    rw [hconj, hd1]; simpa using hb
  exact ⟨hxB, fun a ha => sec9m_commutator_mem_B hctx hxL hxB ht0mem a ha⟩

theorem sec9m_autL (h6 : Asc82Tab6M) (hctx : Sec9Ctx G t L S z g B t₀) :
    Nonempty (↥(autIn L B) ≃* alternatingGroup (Fin 6)) ∧
      ∀ b b' : ↥B, b ≠ 1 → b' ≠ 1 → ∃ k ∈ autIn L B, k b = b' := by
  have hLM : IsOm6M L := ⟨hctx.toSec3SettingLB.component.isQuasisimple, hctx.omega6m⟩
  have hBL : B ≤ L := fun b hb => (hctx.B_le hb).1
  obtain ⟨P0, hP0, hBP0⟩ := sec68_exists_sylow_ge (H := L) hctx.B_e16.1.isPGroup hBL
  obtain ⟨haut, htrans, -⟩ := h6.aut_B G L hLM P0 hP0 B hBP0 hctx.B_e16
  refine ⟨haut, fun b b' hb hb' => ?_⟩
  have hbG : (b : G) ≠ 1 := fun h => hb (Subtype.ext h)
  have hb'G : (b' : G) ≠ 1 := fun h => hb' (Subtype.ext h)
  obtain ⟨n, hn, hnconj⟩ := htrans (b : G) b.2 hbG (b' : G) b'.2 hb'G
  refine ⟨B.normalizerMonoidHom ⟨n, hn.2⟩, ?_, ?_⟩
  · rw [autIn]
    refine Subgroup.mem_map.mpr ⟨⟨n, hn.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact hn.1
  · ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hnconj

theorem sec9m_autIn_le (hT : Asc82Tab9M) (h6 : Asc82Tab6M) (hctx : Sec9Ctx G t L S z g B t₀) :
    autIn L B ≤ autIn (centMod (Asub9 t t₀ B) B) B := by
  let K : Subgroup (MulAut ↥B) := autIn L B
  let H : Subgroup (MulAut ↥B) := autIn (centMod (Asub9 t t₀ B) B) B
  have hK6 : Nonempty (↥K ≃* alternatingGroup (Fin 6)) := (sec9m_autL h6 hctx).1
  have htop : (⊤ : Subgroup ↥K) ≤ H.comap K.subtype := by
    rw [← sec9m_closure_two hK6, Subgroup.closure_le]
    intro k hk
    change (k : MulAut ↥B) ∈ H
    obtain ⟨m, hm⟩ := hk
    obtain ⟨x, hxL, hxN, hxφ⟩ := sec9m_mem_autIn.mp k.2
    let X : Subgroup G := L ⊓ normalizer (B : Set G)
    let xK : ↥X := ⟨x, hxL, hxN⟩
    let ρ : ↥X →* MulAut ↥B := B.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)
    have hρx : ρ xK = (k : MulAut ↥B) := by
      ext b
      change ((B.normalizerMonoidHom (Subgroup.inclusion inf_le_right xK)) b : ↥B).val
        = ((k : MulAut ↥B) b : ↥B).val
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
      exact (hxφ b).symm
    have hm' : (ρ xK) ^ (2 ^ m) = 1 := by
      rw [hρx]
      simpa [Subgroup.coe_pow] using congrArg Subtype.val hm
    obtain ⟨y, hy2, hyρ⟩ := sec9m_exists_twoPart ρ xK hm'
    obtain ⟨r, hyr⟩ := hy2
    have hyr' : (y : G) ^ (2 ^ r) = 1 := by
      have h := congrArg Subtype.val hyr
      simpa [Subgroup.coe_pow] using h
    have hyNmod : (y : G) ∈ centMod (Asub9 t t₀ B) B :=
      sec9m_lift hT hctx y.2.1 y.2.2 hyr'
    refine sec9m_mem_autIn.mpr ⟨(y : G), hyNmod, y.2.2, fun b => ?_⟩
    rw [show (k : MulAut ↥B) = ρ y by rw [← hρx, hyρ]]
    change ((B.normalizerMonoidHom (Subgroup.inclusion inf_le_right y)) b : ↥B).val
      = (y : G) * (b : G) * (y : G)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
  intro k hk
  have hmem : K.subtype (⟨k, hk⟩ : ↥K) ∈ H :=
    Subgroup.mem_comap.mp (htop (Subgroup.mem_top _))
  change k ∈ H
  exact hmem

end CFSG.OddStandard.SmallF3.Omega
