module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusLevi
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusModel
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusBorel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSylow
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpAut
public import Certificates.Certificate2326

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace OmCover

variable {A : Type} [Group A] {Y P : Subgroup A} {r : ℕ} {K : Type} [Field K] {b c : K} {s : ℕ}
  {d : Fin (s + 1) → ℕ} (C : OmCover Y P r K b c d)

@[expose] noncomputable def autHom :
    ↥(Subgroup.normalizer (Y : Set A)) →*
      MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) :=
  (MulAut.congr C.ρ).symm.toMonoidHom.comp Y.normalizerMonoidHom

theorem coe_ρ_autHom (β : ↥(Subgroup.normalizer (Y : Set A)))
    (g : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
    ((C.ρ (C.autHom β g) : ↥Y) : A) = (β : A) * ((C.ρ g : ↥Y) : A) * (β : A)⁻¹ := by
  have h : C.ρ (C.autHom β g) = Y.normalizerMonoidHom β (C.ρ g) := by
    simp [autHom, MulAut.congr_symm_apply]
  rw [h, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem autHom_pow_eq_one (β : ↥(Subgroup.normalizer (Y : Set A))) {p k : ℕ}
    (hβ : (β : A) ^ p ^ k = 1) : C.autHom β ^ p ^ k = 1 := by
  have h : β ^ p ^ k = 1 := Subtype.ext (by simpa using hβ)
  rw [← map_pow, h, map_one]

theorem odd_orderOf_autHom (β : ↥(Subgroup.normalizer (Y : Set A))) {p k : ℕ} (hp : Odd p)
    (hβ : (β : A) ^ p ^ k = 1) : Odd (orderOf (C.autHom β)) :=
  (hp.pow (n := k)).of_dvd_nat (orderOf_dvd_of_pow_eq_one (C.autHom_pow_eq_one β hβ))

theorem centralizes_of_autHom_eq_one (γ : ↥(Subgroup.normalizer (Y : Set A)))
    (h : C.autHom γ = 1) : ∀ y ∈ Y, (γ : A) * y = y * γ := by
  intro y hy
  obtain ⟨g, hg⟩ := C.ρ.surjective ⟨y, hy⟩
  have h1 := C.coe_ρ_autHom γ g
  rw [h, MulAut.one_apply, hg] at h1
  have h2 : (y : A) = (γ : A) * y * (γ : A)⁻¹ := h1
  calc (γ : A) * y = (γ : A) * y * (γ : A)⁻¹ * γ := by group
    _ = y * γ := by rw [← h2]

theorem autHom_mem_orthParab (β : ↥(Subgroup.normalizer (Y : Set A)))
    (hβP : (β : A) ∈ Subgroup.normalizer (P : Set A))
    {x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))}
    (hx : x ∈ orthParab r (minusTailForm K b c) d) :
    C.autHom β x ∈ orthParab r (minusTailForm K b c) d := by
  rw [C.mem_flag_iff, C.coe_ρ_autHom]
  exact (Subgroup.mem_normalizer_iff.mp hβP _).mp ((C.mem_flag_iff x).mp hx)

variable [Finite A] [Finite K] [CharP K 2]

theorem exists_radical (β : ↥(Subgroup.normalizer (Y : Set A)))
    (hβP : (β : A) ∈ Subgroup.normalizer (P : Set A)) (hW : WCent P (β : A))
    (x : ↥(orthParab r (minusTailForm K b c) d)) (hx : C.toHat x ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P)) :
    ∃ u : ↥(orthParab r (minusTailForm K b c) d), u ∈ C.toHat.ker ∧
      (u : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) =
        C.autHom β (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) *
          (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))))⁻¹ := by
  have hxP : ((C.ρ (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : ↥Y) : A) ∈
      P := (C.mem_flag_iff _).mp x.2
  obtain ⟨z, hz, hzeq⟩ := hW _ hxP hx
  have hux : C.autHom β (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) ∈
      orthParab r (minusTailForm K b c) d := C.autHom_mem_orthParab β hβP x.2
  refine ⟨⟨_, Subgroup.mul_mem _ hux (Subgroup.inv_mem _ x.2)⟩, ?_, rfl⟩
  have e1 : ((C.ρ (C.autHom β (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) *
      (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))))⁻¹) : ↥Y) : A) =
      (β : A) * ((C.ρ (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : ↥Y) : A) *
        (β : A)⁻¹ * ((C.ρ (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
          ↥Y) : A)⁻¹ := by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, C.coe_ρ_autHom]
  have htoP : C.toP ⟨_, Subgroup.mul_mem _ hux (Subgroup.inv_mem _ x.2)⟩ = z := by
    apply Subtype.ext
    rw [coe_toP]
    exact e1.trans hzeq.symm
  rw [C.ker_toHat_eq, Subgroup.mem_comap, htoP]
  exact hz

theorem omNormFix_autHom (hd : OrthCuts r d) (hr : 3 ≤ r)
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hPY : P ≤ Y)
    (β : ↥(Subgroup.normalizer (Y : Set A))) (hβP : (β : A) ∈ Subgroup.normalizer (P : Set A))
    (hW : WCent P (β : A)) : OmNormFix hr hirr hd (C.autHom β) := by
  refine ⟨fun x hx => C.autHom_mem_orthParab β hβP hx, fun l B => ?_, fun hm g hg => ?_⟩
  · obtain ⟨u, hu, hue⟩ := C.exists_radical β hβP hW (orthLeviSL hd (minusTailForm K b c) hr l B)
      (C.toHat_orthLeviSL_mem_wSup hd hPY hr l B)
    exact ⟨u, C.orthBlockHom_eq_one_of_mem_ker_toHat hd hr hPY l hu, hue⟩
  · obtain ⟨u, hu, hue⟩ := C.exists_radical β hβP hW (resLevi hd hr hirr ⟨g, hg⟩)
      (C.toHat_resLevi_mem_wSup hd hPY hr hirr hm ⟨g, hg⟩)
    exact ⟨u, C.orthResHom_eq_one_of_mem_ker_toHat hd hr hirr hPY hm hu, hue⟩

include C in
theorem exists_big_block (hd : OrthCuts r d) (hr : 3 ≤ r) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (hPY : P ≤ Y) (hna : ∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) :
    (∃ l : Fin s, 2 ≤ d l.succ - d l.castSucc) ∨ 1 ≤ r - d (Fin.last s) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hk, hm⟩ := hcon
  have hani := anisotropic_minusTailForm hirr
  have hlast : d (Fin.last s) = r := by
    have := hd.last
    omega
  have hd1 : ∀ l : Fin s, d l.succ = d l.castSucc + 1 := fun l => by
    have := hd.mono (Fin.castSucc_lt_succ (i := l))
    have := hk l
    omega
  have hdi : ∀ (n : ℕ) (hn : n < s + 1), d ⟨n, hn⟩ = n := by
    intro n
    induction n with
    | zero => intro hn; exact hd.zero
    | succ n ih =>
      intro hn
      have h1 := hd1 ⟨n, by omega⟩
      have h2 := ih (by omega)
      change d ⟨n + 1, hn⟩ = d ⟨n, by omega⟩ + 1 at h1
      omega
  have hsr : s = r := by
    have := hdi s (Nat.lt_succ_self s)
    have h2 : d (Fin.last s) = s := this
    omega
  have hB : ∀ x : ↥(orthParab r (minusTailForm K b c) d),
      ((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) ∈ tailBorel r (minusTailForm K b c) := by
    intro x
    rw [mem_tailBorel]
    refine ⟨x.1.2, fun i hi1 hir => ?_⟩
    have := mem_orthParab.1 x.2 ⟨i, by omega⟩
    rwa [hdi i (by omega)] at this
  set U₁ : Subgroup ↥(orthParab r (minusTailForm K b c) d) :=
    (tailUnipotent r (minusTailForm K b c)).comap
      ((orthElementaryGroup (quadTail r (minusTailForm K b c))).subtype.comp
        (orthParab r (minusTailForm K b c) d).subtype) with hU₁
  have hU₁n : U₁.Normal := ⟨fun n hn g => by
    have hN := tailUnipotent_normal hani (r := r) (qA := minusTailForm K b c)
    have := hN.conj_mem ⟨((n : ↥(orthParab r (minusTailForm K b c) d)) :
      ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))).1,
        tailUnipotent_le_tailBorel hani hn⟩ (Subgroup.mem_subgroupOf.2 hn)
      ⟨((g : ↥(orthParab r (minusTailForm K b c) d)) :
        ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))).1, hB g⟩
    exact Subgroup.mem_subgroupOf.1 this⟩
  have hU₁p : IsPGroup 2 U₁ := by
    intro n
    have hP2 := isPGroup_tailUnipotent (p := 2) hani (r := r)
    obtain ⟨k, hk'⟩ := hP2 ⟨((n : ↥(orthParab r (minusTailForm K b c) d)) :
      ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))), Subgroup.mem_subgroupOf.2 n.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥((tailUnipotent r (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail r (minusTailForm K b c)))) => z.1) hk'
    simpa using this
  obtain ⟨x, hxP, y, hyP, hxy⟩ := hna
  apply hxy
  obtain ⟨x', hx'⟩ := C.toP_surjective hPY ⟨x, hxP⟩
  obtain ⟨y', hy'⟩ := C.toP_surjective hPY ⟨y, hyP⟩
  have hcomm : ⁅x', y'⁆ ∈ U₁ := by
    have := commutator_mem_tailUnipotent hr hirr (hB x') (hB y')
    simpa [hU₁, commutatorElement_def] using this
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : U₁.map C.toP ≤ CFSG.pCore 2 ↥P :=
    le_sSup ⟨hU₁n.map _ (C.toP_surjective hPY), hU₁p.map _⟩
  have hmem : C.toP ⁅x', y'⁆ ∈ CFSG.pCore 2 ↥P := hle ⟨_, hcomm, rfl⟩
  rw [map_commutatorElement, hx', hy'] at hmem
  refine ⟨_, hmem, ?_⟩
  simp [commutatorElement_def]

end OmCover

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
