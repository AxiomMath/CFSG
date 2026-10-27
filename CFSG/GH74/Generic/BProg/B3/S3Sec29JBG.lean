module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29JBD8
public import CFSG.GH74.Generic.BProg.B3.S3Sec29JBA
public import CFSG.GH74.Generic.BProg.B3.S3Sec29G
public import CFSG.GH74.Generic.BProg.B3.S3Sec29A4
public import CFSG.GH74.Generic.BProg.B3.S3Sec29B7
public import CFSG.GH74.Generic.BProg.B3.S3Sec29E4
public import CFSG.GH74.Generic.BProg.B3.S3SD7Dich

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure S18bInputsB (G : Type) [Group G] [Finite G] : Prop where
  kg31e : Kg31e G
  kg21d : Kg21d
  s16c : S3Sec29C.S16cKG

namespace S3Sec29JB

theorem exists_J_of_H29B
    (hKG : Sec29KGw G) (hS : S18bInputsB G)
    {x a y : G} {K A D J₀ B Q : Subgroup G} (hc : Ctx21 G x K A a D J₀)
    (hB : H29 G x K A B Q y) :
    ∃ J : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) J ∧ IsA7Bar J ∧
      (∀ J'' : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) J'' → IsA7Bar J'' →
        J'' = J) ∧
      B ≤ normalizer (J : Set G) ∧
      ∃ (e : kBar J ≃* alternatingGroup (Fin 7)) (F₀ F₁ : Subgroup (Equiv.Perm (Fin 7))),
        ImageF0F1 B J e F₀ F₁ := by
  obtain ⟨b, hbB, D', J', htype, hobs⟩ :=
    lemma293w hKG hc hB.shape hB.ext hB.rankB hB.notG hB.y_mem hB.y_ord
  have h0 : Ctx29w G x K A B Q y b D' J' := S3Sec29G.ctx29w_of_H29 hB hbB hobs
  have h295 : B ⊓ cSec K ⊓ cSec J' = ⊥ := lemma295w_core hKG.noL3Step h0
  obtain ⟨-, D'', J'', h1, htype', h295', h296'⟩ := lemma296w h0 htype h295
  obtain ⟨R, hR, hQR⟩ := exists_R_L (y := y) (L1 K y) hB.Q_syl.isPGroup
  have hRB : ∀ g ∈ B ⊓ cSec K, ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun g hg r hr =>
    mul_mem (mul_mem (hQR (hB.B0_le_Q hg)) hr) (inv_mem (hQR (hB.B0_le_Q hg)))
  have h297a : ∀ r ∈ R ⊓ centralizer ({x} : Set G), r * r ∈ Q → r ∈ Q ∨ r * y⁻¹ ∈ Q :=
    (part_a_L1 h1 hR hQR).2.2
  have h297c : Q ⊓ ((R ⊓ Zstar (Jstar B J'')) ⊔ zpowers y) = ⊥ :=
    S3Sec29Cw.part_c (k26_proved G) h1 h295' h296' hRB
  have hMu : MuPkgL K A Q y (L1 K y) := muPkgL1_of_ctx29w h1
  have hJL : J'' ≤ cSec (L1 K y) := le_cSec_L1 (S3Sec29Cw.J_comp h1) h296'
  have h298 : ¬ HasSL2Model (↥J'' ⧸ pPrimeCore 2 ↥J'') Odd :=
    lemma298wL hS.kg31e hS.kg21d hS.s16c h1 h295' (B_le_normalizer_L1 h1)
      (Q_le_normalizer_L1 h1) (y_mem_cSec_L1 K y) hJL hR hRB h297a h297c hMu
  obtain ⟨hA7, hBN, huniq, e, F₀, F₁, hF⟩ := lemma299w a7Dich_proved h1 htype' h298
  exact ⟨J'', S3Sec29Cw.J_comp h1, hA7, huniq, hBN, e, F₀, F₁, hF⟩

end S3Sec29JB

theorem lemma2910_fullB
    (hKG : Sec29KGw G) (hS : S18bInputsB G) : Lemma2910Full G := by
  intro x a y K A D J₀ B₁ Q₁ hc hB₁
  obtain ⟨J, hJc, hJA, huniq, -⟩ := S3Sec29JB.exists_J_of_H29B hKG hS hc hB₁
  refine ⟨J, hJc, hJA, huniq, fun B Q hB => ?_⟩
  obtain ⟨J', hJ'c, hJ'A, -, hBN, hF⟩ := S3Sec29JB.exists_J_of_H29B hKG hS hc hB
  obtain rfl : J' = J := huniq J' hJ'c hJ'A
  exact ⟨hBN, hF⟩

end CFSG.GH74.Generic.BProg.B3
