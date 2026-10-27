module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step7
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Step12Input
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step6b
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8E32Step8

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

theorem mem_closure_sq (H : L83Hyp h) (x : X) : x ∈ closure {y : X | ∃ g : X, y = g ^ 2} := by
  have hN : (closure {y : X | ∃ g : X, y = g ^ 2}).Normal := by
    constructor
    intro n hn k
    have hle : closure {y : X | ∃ g : X, y = g ^ 2} ≤
        (closure {y : X | ∃ g : X, y = g ^ 2}).comap (MulAut.conj k).toMonoidHom := by
      rw [closure_le]
      rintro _ ⟨g, rfl⟩
      show (MulAut.conj k) (g ^ 2) ∈ closure {y : X | ∃ g : X, y = g ^ 2}
      exact subset_closure ⟨k * g * k⁻¹, by rw [map_pow, MulAut.conj_apply]⟩
    exact hle hn
  have := H.setting.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (closure {y : X | ∃ g : X, y = g ^ 2})
    with h1 | h1
  · exfalso
    obtain ⟨u, v, huv⟩ := H.setting.2.1
    have hsq : ∀ g : X, g * g = 1 := fun g => by
      have : g ^ 2 ∈ closure {y : X | ∃ g : X, y = g ^ 2} := subset_closure ⟨g, rfl⟩
      rw [h1, mem_bot, pow_two] at this
      exact this
    apply huv
    rw [(inv_eq_of_mul_eq_one_right (hsq (u * v))).symm, mul_inv_rev,
      inv_eq_of_mul_eq_one_right (hsq u), inv_eq_of_mul_eq_one_right (hsq v)]
  · rw [h1]
    exact mem_top x

namespace Q3Data

variable (d : Q3Data H)
include d

namespace LClass

variable {d} (L : d.LClass)

theorem E0of_eq (hq : h.IsQ3) (hF : Cat8.Q3Facts) : Eight.E0of L.c = d.E0 := by
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  have hle : Eight.E0of L.c ≤ d.E0 := by
    rw [Eight.E0of, closure_le]
    rintro _ ⟨i, j, rfl⟩
    exact d.mul_mem_E0_of_not_mem (L.c_mem_E i) (L.c_mem_E j) (L.c_not_mem_E0 i)
      (L.c_not_mem_E0 j)
  have hcard : Nat.card (Eight.E0of L.c) = 16 := (L.base hq hF).card_E0
  exact eq_of_le_of_card_ge hle (by rw [hcard, d.card_E0 hCF1 hCF2])

end LClass

theorem nonempty_conf (hq : h.IsQ3) (hF : Cat8.Q3Facts) : Nonempty (Eight.E32Conf X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  obtain ⟨L, U, hRU, hW, hW'⟩ := d.exists_good hq hF
  have hBE : Eight.Eof (L.base hq hF).c = d.E := L.Eof_eq
  have hBN : normalizer ((Eight.Eof (L.base hq hF).c : Subgroup X) : Set X) = d.NE :=
    L.normalizer_Eof
  have hE0 : Eight.E0of (L.base hq hF).c = d.E0 := L.E0of_eq hq hF
  have hnf := d.not_fused hq hF
  have haS := L.πa_isSwap hq hF (hW _ (hRU (d.RM_le_R d.a_mem_RM)))
  have hπ : ∀ n : ↥(normalizer ((Eight.Eof (L.base hq hF).c : Subgroup X) : Set X)),
      (L.base hq hF).π n = L.πN ⟨n, hBN ▸ n.2⟩ := fun _ => rfl
  refine ⟨{
    toE32Base := L.base hq hF
    U := U
    U_sylow := ⟨U, rfl⟩
    c_mem := ?_
    π_W := ?_
    π_W_onto := ?_
    π_ker := ?_
    W_ne := ?_
    fus_a := ?_
    fus_z := ?_
    fus_sc := ?_
    sq := ?_ }⟩
  · intro i
    exact hRU (d.E_le_R (L.c_mem_E i))
  · intro n hn
    rw [hπ]
    exact hW _ hn
  · intro t ht
    obtain ⟨n, hn, hnt⟩ := hW' t ht
    exact ⟨⟨n, hBN.symm ▸ n.2⟩, hn, by rw [hπ]; exact hnt⟩
  · intro n hn h1
    rw [hπ] at h1
    have h2 := (L.πN_eq_one_iff _).mp h1
    show (n : X) ∈ Eight.Eof (L.base hq hF).c
    exact hBE.symm.le
      (d.mem_E_of_comm_of_mem hCF1 hCF2 U.isPGroup' hn fun e he => (h2 e he).symm)
  · show (U : Subgroup X) ⊓ normalizer ((Eight.Eof (L.base hq hF).c : Subgroup X) : Set X) ≠ U
    rw [hBN]
    exact L.W_ne hq hF hRU hW
  · intro n hn hn2 hsw
    rw [hπ] at hsw
    obtain ⟨m, hm, e₁, he₁, hme⟩ := L.exists_conj_aE hq hF haS (hBN ▸ n.2) hn2 hsw
    have haN := d.a_mem_NE
    have he : (m : X)⁻¹ * (h.a * e₁⁻¹ * h.a⁻¹) * m ∈ d.E := by
      have h1 : h.a * e₁⁻¹ * h.a⁻¹ ∈ d.E :=
        (mem_normalizer_iff.mp haN _).mp (inv_mem he₁)
      have := (mem_normalizer_iff.mp (inv_mem hm) _).mp h1
      rwa [inv_inv] at this
    have hen : (m : X)⁻¹ * (h.a * e₁⁻¹ * h.a⁻¹) * m * n = m⁻¹ * h.a * m := by
      have hn' : (n : X) = m⁻¹ * (h.a * e₁) * m := by
        rw [← hme]
        group
      rw [hn']
      group
    refine ⟨_, hBE ▸ he, ?_, ?_⟩
    · rw [hen, show (m : X)⁻¹ * h.a * m * ((m : X)⁻¹ * h.a * m) = m⁻¹ * (h.a * h.a) * m by
        group, Six.a_mul_a_self h, mul_one, inv_mul_cancel]
    · intro g e' he'
      rw [hen, show g⁻¹ * ((m : X)⁻¹ * h.a * m) * g = (m * g)⁻¹ * h.a * (m * g) by group]
      exact d.a_not_conj_E hq hF (m * g) (hBE ▸ he')
  · intro e he he1 g n hng hn hsw
    rw [hπ] at hsw
    rw [hE0] at he
    obtain ⟨g₀, hg₀⟩ := (d.E0_conj hq hF he).resolve_left he1
    have hn2 : (n : X) * n = 1 := by
      rw [hng, show g⁻¹ * e * g * (g⁻¹ * e * g) = g⁻¹ * (e * e) * g by group,
        d.E0_sq hCF1 hCF2 he, mul_one, inv_mul_cancel]
    obtain ⟨m, hm, e₁, he₁, hme⟩ := L.exists_conj_aE hq hF haS (hBN ▸ n.2) hn2 hsw
    have hae2 : h.a * e₁ * (h.a * e₁) = 1 := by
      rw [← hme, show (m : X) * n * (m : X)⁻¹ * ((m : X) * n * (m : X)⁻¹) =
        m * (n * n) * m⁻¹ by group, hn2, mul_one, mul_inv_cancel]
    have hf : (g₀ * g * m⁻¹)⁻¹ * (d.tau * d.z) * (g₀ * g * m⁻¹) = h.a * e₁ := by
      rw [← hme, hng, ← hg₀]
      group
    rcases d.aE_conj hq hF he₁ hae2 with ⟨f, hf'⟩ | ⟨f, hf'⟩ | ⟨f, hf'⟩
    · apply (hnf (f * (g₀ * g * m⁻¹)⁻¹)).2.2.1
      rw [show (f * (g₀ * g * m⁻¹)⁻¹)⁻¹ * h.a * (f * (g₀ * g * m⁻¹)⁻¹) =
        (g₀ * g * m⁻¹) * (f⁻¹ * h.a * f) * (g₀ * g * m⁻¹)⁻¹ by group, hf', ← hf]
      group
    · apply (hnf (f * (g₀ * g * m⁻¹)⁻¹)).2.2.2.2.1
      rw [show (f * (g₀ * g * m⁻¹)⁻¹)⁻¹ * d.b * (f * (g₀ * g * m⁻¹)⁻¹) =
        (g₀ * g * m⁻¹) * (f⁻¹ * d.b * f) * (g₀ * g * m⁻¹)⁻¹ by group, hf', ← hf]
      group
    · apply (hnf (f * (g₀ * g * m⁻¹)⁻¹)).2.2.2.2.2
      rw [show (f * (g₀ * g * m⁻¹)⁻¹)⁻¹ * (d.b * d.z) * (f * (g₀ * g * m⁻¹)⁻¹) =
        (g₀ * g * m⁻¹) * (f⁻¹ * (d.b * d.z) * f) * (g₀ * g * m⁻¹)⁻¹ by group, hf', ← hf]
      group
  · intro e he g hg
    rw [hE0] at he ⊢
    rw [hBE] at hg
    exact d.E0_strongly_closed hq hF he g hg
  · exact H.mem_closure_sq _

theorem false_of_q3 (hq : h.IsQ3) (hF : Cat8.Q3Facts) (h12 : GS83Step12Input) : False :=
  (d.nonempty_conf hq hF).elim fun C => h12 X h H hq C

end Q3Data

theorem false_of_q3 (H : L83Hyp h) (hq : h.IsQ3) (hF : Cat8.Q3Facts)
    (h12 : GS83Step12Input) : False := by
  obtain ⟨d⟩ := H.exists_Q3Data hq hF.simple hF.inner hF.out hF.f2 hF.l0 hF.conf
  exact d.false_of_q3 hq hF h12

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
