module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
public import Certificates.Certificate5180
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34ModelS
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.AGLEmbedding

namespace KFactProofs.L34AutExp

open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

theorem exp27 :
    ∀ x ∈ R, x ^ 27 = 1 → x ^ 3 = 1 := by
  have h : l34AutCheck enumS.tabs enumR.tabs = true := Certificates.certificate5180
  simp only [l34AutCheck, Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hexp, -⟩ := h
  exact fun x hx h27 => expOK_spec enumerates_R hexp hx h27

theorem pow_three_eq_one_of_pow_three_pow_eq_one
    {r : Equiv.Perm (Fin 42)} (hr : r ∈ R) {n : ℕ}
    (hn : r ^ 3 ^ n = 1) : r ^ 3 = 1 := by
  let r' : ↥R := ⟨r, hr⟩
  have hn' : r' ^ 3 ^ n = 1 := Subtype.ext (by simpa using hn)
  have hd1 : orderOf r' ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn'
  have hd2 : orderOf r' ∣ 241920 := card_R ▸ orderOf_dvd_natCard r'
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd1
  have hk3 : k ≤ 3 := by
    by_contra hlt
    have h81 : 3 ^ 4 ∣ 241920 := (pow_dvd_pow 3 (by omega)).trans (hk ▸ hd2)
    norm_num at h81
  have h27 : orderOf r' ∣ 27 := hk ▸ (pow_dvd_pow 3 hk3 : 3 ^ k ∣ 3 ^ 3)
  have h27' : r' ^ 27 = 1 := orderOf_dvd_iff_pow_eq_one.1 h27
  exact exp27 r hr (by simpa using congrArg Subtype.val h27')

end KFactProofs.L34AutExp

open CFSG.ComponentClassification.PSL3Four

theorem kFactL34AutExp :
    KFactL34AutExp := by
  intro K _ _ hK f ⟨n, hf⟩
  obtain ⟨ε⟩ := KFactProofs.L34ModelS.nonempty_mulEquiv_S_of_isLinThreeFour hK
  obtain ⟨e, -, -⟩ := full_automorphism_action
  let ψ : MulAut K ≃* ↥R := (MulAut.congr ε).trans e.symm
  have hψ : (ψ f : Equiv.Perm (Fin 42)) ^ 3 ^ n = 1 := by
    have h : ψ f ^ 3 ^ n = 1 := by rw [← map_pow, hf, map_one]
    simpa using congrArg Subtype.val h
  have h3 := KFactProofs.L34AutExp.pow_three_eq_one_of_pow_three_pow_eq_one (ψ f).2 hψ
  apply ψ.injective
  rw [map_pow, map_one]
  exact Subtype.ext (by simpa using h3)

end CFSG.AGLEmbedding
