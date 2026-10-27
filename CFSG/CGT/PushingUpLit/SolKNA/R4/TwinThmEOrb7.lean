module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmESev2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOrb2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOrb5
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOrb6

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped commutatorElement

namespace ThmE

section Orb7



variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.goodFourD_of_noncommute (h : E18_6 r) (h4 : E18_4C r)
    (c : MinCex r Ω K S R W H) {z g t : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W)
    (hzH : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hSylz : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
      (Subgroup.centralizer ({z} : Set G)))
    (hg : g ∉ H) (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t) :
    TwinThmEW.GoodFourWD (S : Subgroup G) H W t := by
  classical
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hA : EtaAbelian Ω := TwinThmEW.etaAbelian_of_gen hΩ
  have hM : EtaMeet Ω := TwinThmEW.etaMeet_of_gen hΩ
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨-, hWS, hWn⟩ := c.stand.hW
  obtain ⟨K', hK'tw, hne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  exact goodFourD_of_noncommute_of' (K' := K') (R' := R') (z := z) (g := g) (t := t) hΩ
    c.W_abelian
    (fun M₁ M₂ R₁ R₂ hM₁ hM₂ hne hR₁ hR₁M hR₁S hR₂ hR₂M hR₂S =>
      commutes_inf_S' hΩ hM₁ hM₂ hne hR₁ hR₁M hR₁S hR₂ hR₂M hR₂S)
    (fun hM' hR₀ hR₀M hR₀S => by
      obtain ⟨-, u, hu, hu4⟩ := c.exists_order_four_of_inf_W hA hM hM' hR₀ hR₀M hR₀S
      exact ⟨u, hu, hu4⟩)
    (inf_S_eq_of_mem_RSet' hΩ c.stand.mem hRR hRK hRS) (Sec6Gen.isQuatSub_of_mem_RSet hΩ hRR)
    (fun hx1 => c.centralizer_ne_top h hx1)
    (fun hK₃tw hK₄tw hne43 hR₃ hR₃K hR₃S hR₄ hR₄K hR₄S hK₄tw' x hx1 hx2 hA2 hsup hXne =>
      (c.renameTwin hK₃tw hR₃ hR₃K hR₃S hK₄tw hne43 hR₄ hR₄K hR₄S).centralizer_le_H' h4 hK₄tw'
        hne43 hR₄ hR₄K hR₄S hA2 ⟨x, hx1, hx2, rfl⟩ hsup hXne)
    c.stand.mem hRR hRK hRS hWS hWn hK'tw hne hR' hR'K' hR'S
    (inf_S_eq_of_mem_RSet' hΩ hK'tw.1 hR' hR'K' hR'S) hz ht htS hnc
    (c.exists_two_twins hz hzW hzH hSylz hg ht htS hnc (K' := K'))

theorem MinCex.orbit4_false (c : MinCex r Ω K S R W H) {z g t d₁ d₂ : G}
    (hz : IsUniqueInvolution K z) (hg : g ∉ H) (ht : t = g * z * g⁻¹)
    (hCS : ∀ x ∈ (S : Subgroup G), t * x = x * t → x ∈ conjSub g (S : Subgroup G))
    (hCSyl : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G))
      (Subgroup.centralizer ({t} : Set G) ⊓ H))
    (g₁ : GoodInv H t d₁) (g₂ : GoodInv H t d₂) (g₃ : GoodInv H t (d₁ * d₂))
    (hc : d₁ * d₂ = d₂ * d₁) (hd₁W : d₁ ∈ W) (hd₂W : d₂ ∈ W)
    (hshape : TwinThmEW.D4Shape (S : Subgroup G) t d₁ d₂)
    (m₁ : conjSub d₁ (conjSub g K) ≠ conjSub g K) (m₂ : conjSub d₂ (conjSub g K) ≠ conjSub g K)
    (m₃ : conjSub (d₁ * d₂) (conjSub g K) ≠ conjSub g K) : False := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hA : EtaAbelian Ω := TwinThmEW.etaAbelian_of_gen hΩ
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨-, hWS, hWn⟩ := c.stand.hW
  have hSH : (S : Subgroup G) ≤ H := c.sylow_le hA
  have hbad := c.hbad_of_conj hz hg
  rw [← ht] at hbad
  obtain ⟨A, hA₁, -, hAN, hAD⟩ := hshape
  have hK₀ : conjSub g K ∈ Ω := hΩ.conjInvariant g K c.stand.mem
  have hK₀t : IsUniqueInvolution (conjSub g K) t := by rw [ht]; exact hz.conj g
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ c.stand.mem hRR hRK
  have hR₀ : IsSylow2In (conjSub g R) (conjSub g K) := hRsyl.conj g
  have hq : IsQuatSub (conjSub g R) :=
    Sec6Gen.isQuatSub_of_mem_RSet hΩ (RSet.conj hΩ.conjInvariant hRR g)
  have hS₁ : IsPGroup 2 ↥(conjSub g (S : Subgroup G)) := isPGroup_conjSub g S.isPGroup'
  have hR₀S : conjSub g R ≤ conjSub g (S : Subgroup G) := conjSub_mono hRS
  have hd₁S : d₁ ∈ conjSub g (S : Subgroup G) := hCS d₁ (hWS hd₁W) g₁.comm_t.symm
  have hd₂S : d₂ ∈ conjSub g (S : Subgroup G) := hCS d₂ (hWS hd₂W) g₂.comm_t.symm
  have hF6 : ∀ v ∈ conjSub g (S : Subgroup G), v * t = t * v → v ∈ H → v ∈ (S : Subgroup G) := by
    intro v hvS₁ hvt hvH
    have hPS₁ : (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) ≤ conjSub g (S : Subgroup G) :=
      fun x hx => hCS x hx.1 (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
    have hvC : v ∈ Subgroup.centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hvt
    have hM2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) ⊔
        Subgroup.zpowers v) :=
      hS₁.to_le (sup_le hPS₁ (Subgroup.zpowers_le.mpr hvS₁))
    have hMle : (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) ⊔ Subgroup.zpowers v ≤
        Subgroup.centralizer ({t} : Set G) ⊓ H :=
      sup_le (le_inf inf_le_right (inf_le_left.trans hSH))
        (Subgroup.zpowers_le.mpr ⟨hvC, hvH⟩)
    have heq := hCSyl.eq_of_le hM2 hMle le_sup_left
    have hv : v ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) ⊔ Subgroup.zpowers v :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
    rw [heq] at hv
    exact hv.1
  exact orbit4_core' (S := (S : Subgroup G)) hΩ hK₀ hK₀t hR₀.1 hq hS₁ hR₀S g₁ g₂ g₃ hc hd₁S hd₂S m₁ m₂ m₃
    hF6 (fun u hu hu4 => hbad _ hK₀ hK₀t u hu hu4) hA₁ hAN hAD

end Orb7

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
