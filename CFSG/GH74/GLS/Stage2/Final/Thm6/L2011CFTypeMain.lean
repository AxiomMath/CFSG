module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CFTypeStmt
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CFD411
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CFTrans
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011C413Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2

theorem cfTypeAut_of_data (h93 : Ivk93Pair) (h413 : IVK413H) (h411 : Data411Clauses) :
    CFTypeAut := by
  intro K _ _ hsimp hnab hGH x hx q E₁ E₂ hcfg X hX hY
  obtain ⟨Y₀, hY₀X, hY₀x, hY₀n, hY₀odd, hY₀ne⟩ := hY
  have hZ := center_trivial_of_simple hsimp hnab
  have hfix := isG2Sp4L4U4_of_concl (h93 K hsimp hGH x hx q E₁ E₂ hcfg)
  have hq3 : 3 < q := by have := hcfg.five; omega
  let K' : Subgroup ↥X := innRange X hX
  have hK'n : K'.Normal := innRange_normal X hX
  let eK : K ≃* ↥K' := MonoidHom.ofInjective (innIn_injective X hX hZ)
  have hfix' : IsG2Sp4L4U4_fixed ↥K' q := isG2Sp4L4U4_of_equiv eK hfix
  have hcen : centralizer (K' : Set ↥X) = ⊥ := centralizer_innRange_eq_bot X hX hZ
  obtain ⟨S, hzS, hz2, hSc⟩ := exists_sylow_cent X hX hZ hx
  have hne := pPrimeCore_ne_bot X hX hZ hY₀X hY₀x hY₀n hY₀odd hY₀ne
  obtain ⟨⟨ε, hε, h8, hLn'⟩, hval2', hpc', hcomp', hle'⟩ :=
    h413 ↥X K' q hK'n hcfg.odd hq3 hfix' hcen (innIn X hX x) (innIn_mem_innRange X hX x)
      ⟨S, hzS, hz2, hSc⟩ hne
  have hLn : IsLnEps 4 K ε q := isLnEps_of_equiv' eK.symm hLn'
  obtain ⟨I₁, I₂, hd⟩ := h411 K ε q hε hcfg.odd hq3 h8 hLn x hx
  have hpair := pair_eq hcfg.odd hcfg hd
  obtain ⟨hc₁, hc₂⟩ := isComponent_I hcfg.five hd
  have hE₁comp : CFSG.IsComponent (E₁.subgroupOf (centralizer ({x} : Set K))) := by
    rcases hpair with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact hc₁
    · rw [h1]; exact hc₂
  refine ⟨⟨ε, hε, h8, hLn⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hd.sup.symm
    · rw [h1, h2, sup_comm]; exact hd.sup.symm
  · intro a ha b hb
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at ha; rw [h2] at hb; exact hd.comm a ha b hb
    · rw [h1] at ha; rw [h2] at hb; exact (hd.comm b hb a ha).symm
  · rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hd.inf
    · rw [h1, h2, inf_comm]; exact hd.inf
  · rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]; exact hd.sl₁
    · rw [h1]; exact hd.sl₂
  · rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]; exact hd.sl₂
    · rw [h2]; exact hd.sl₁
  · exact val2_transport X hX hZ x hval2'
  ·
    intro Y hYX hYx hYn hYodd β hβ k hk
    set C : Subgroup ↥X := centralizer ({innIn X hX x} : Set ↥X) with hC
    let ψ : ↥C →* MulAut K := X.subtype.comp C.subtype
    have hψinj : Function.Injective ψ := fun a b h => Subtype.ext (Subtype.ext h)
    have hψx : ∀ c : ↥C, ψ c x = x := fun c => (mem_centralizer_innIn X hX hZ x c.1).1 c.2
    let Y₁ : Subgroup ↥C := Y.comap ψ
    have hY₁n : Y₁.Normal := ⟨fun n hn g => by
      show ψ (g * n * g⁻¹) ∈ Y
      rw [map_mul, map_mul, map_inv]
      exact hYn (ψ g) g.1.2 (hψx g) (ψ n) hn⟩
    have hYle : Y ≤ ψ.range := fun β hβ =>
      ⟨⟨⟨β, hYX hβ⟩, (mem_centralizer_innIn X hX hZ x _).2 (hYx β hβ)⟩, rfl⟩
    have hmap : Y₁.map ψ = Y := Subgroup.map_comap_eq_self hYle
    have hcard : Nat.card ↥Y₁ = Nat.card ↥Y := by
      calc Nat.card ↥Y₁ = Nat.card ↥(Y₁.map ψ) := (Subgroup.card_map_of_injective hψinj).symm
        _ = Nat.card ↥Y := by rw [hmap]
    have hle : Y₁ ≤ pPrimeCore 2 ↥C := le_sSup ⟨hY₁n, Nat.coprime_two_left.2 (hcard ▸ hYodd)⟩
    obtain ⟨c, hcY₁, rfl⟩ : ∃ c ∈ Y₁, ψ c = β := by
      have : β ∈ Y₁.map ψ := hmap ▸ hβ
      obtain ⟨c, hc, rfl⟩ := this
      exact ⟨c, hc, rfl⟩
    have hcP : (c : ↥X) ∈ (pPrimeCore 2 ↥C).map C.subtype := ⟨c, hle hcY₁, rfl⟩
    have hcP' : (c : ↥X) ∈ (pPrimeCore 2 ↥(C ⊓ K')).map (C ⊓ K').subtype := by
      rw [hpc']
      exact hcP
    have hK₁le : E₁.map (innIn X hX) ≤ C ⊓ K' := map_innIn_le X hX hZ x hcfg.le₁
    have hK₁comp : CFSG.IsComponent ((E₁.map (innIn X hX)).subgroupOf (C ⊓ K')) :=
      isComponent_map_innIn X hX hZ x hcfg.le₁ hE₁comp
    have hg : innIn X hX k ∈ K' ⊓ normalizer (((E₁.map (innIn X hX) : Subgroup ↥X)) : Set ↥X) :=
      ⟨innIn_mem_innRange X hX k, innIn_mem_normalizer_map X hX hk⟩
    have hcomm := hcomp' _ hK₁le hK₁comp (c : ↥X) hcP' (innIn X hX k) hg
    have hmem : (c : ↥X) ∈ centralizer ({innIn X hX k} : Set ↥X) :=
      Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm
    exact (mem_centralizer_innIn X hX hZ k (c : ↥X)).1 hmem

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT
