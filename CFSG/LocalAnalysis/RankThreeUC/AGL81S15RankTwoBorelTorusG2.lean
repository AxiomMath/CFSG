module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBorelTorus
import CFSG.LocalAnalysis.UniquenessCase.UC22S218G2
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.SmithB42G2Id

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.Explicit

theorem hasBorelTorus_cayleyGroup
    {F : Type} [Field F] [Finite F] [CharP F 2] {q : ℕ}
    (hq : q.Prime) (hdvd : q ∣ Nat.card F - 1)
    {U : Subgroup ↥(CFSG.Quasithin.Explicit.cayleyGroup F)}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    HasBorelTorus ↥(CFSG.Quasithin.Explicit.cayleyGroup F) q U := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨m, -, hFc⟩ := FiniteField.card F 2
  set f : ℕ := (m : ℕ)
  have hK : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hFc]
  have hF2 : 2 ≤ Nat.card F := by
    have h := (Finite.one_lt_card : 1 < Nat.card F)
    omega
  have hf : 2 ≤ f := by
    have hq2 : 2 ≤ q := hq.two_le
    have hqle : q ≤ Nat.card F - 1 := Nat.le_of_dvd (by omega) hdvd
    by_contra h
    have hle : f ≤ 1 := by omega
    have h2 : 2 ^ f ≤ 2 := by
      calc 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
        _ = 2 := by norm_num
    omega
  obtain ⟨E, hEtorus, hEea, hEcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s218_g2_model_elemAbelian (K := F)
      (ℓ := q) hq hdvd
  have hD := CFSG.Quasithin.H13.Sec53F.G2.borelAutData_g2 (K := F) hf hK
  have hBT : IsBorelTorus q (posUnipotentSub Tag.G2 F) E :=
    isBorelTorus_of_le_torus (U := posUnipotentSub Tag.G2 F) (H := torusSub Tag.G2 F)
      (E := E) hD.H_comm hD.H_le hD.B_eq hEtorus hEea hEcard
  obtain ⟨ψ, -, hsurj, hker⟩ :=
    CFSG.Quasithin.B42G2Id.exists_adjointGroup_hom_cayleyGroup (K := F) hK hf
  have hkerbot : ψ.ker = ⊥ := hker.trans CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hkerbot
  let φ : ↥(adjointGroup Tag.G2 F) ≃* ↥(cayleyGroup F) :=
    MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  haveI : Finite (ModGL Tag.G2 F) := finite_modGL
  haveI : Finite ↥(adjointGroup Tag.G2 F) := Subtype.finite
  haveI : Finite ↥(cayleyGroup F) := Finite.of_surjective ψ hsurj
  exact HasBorelTorus.of_mulEquiv φ hD.sylow ⟨E, hBT⟩ hU

end CFSG.LocalAnalysis.RankThreeUC.S15

end
