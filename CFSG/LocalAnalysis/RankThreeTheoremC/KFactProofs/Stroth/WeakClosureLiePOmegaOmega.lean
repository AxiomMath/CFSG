module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmegaFrame
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieBlockFrame
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslNonab

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

theorem mem_commutator_of_odd_pow_eq_one {O : Type} [Group O]
    (hsq : ∀ g : O, g ^ 2 ∈ commutator O) {x : O} {n : ℕ} (hn : Odd n) (hx : x ^ n = 1) :
    x ∈ commutator O := by
  obtain ⟨k, rfl⟩ := hn
  have h : x = (x ^ (k + 1)) ^ 2 := by
    rw [← pow_mul]
    calc x = x ^ (2 * k + 1) * x := by rw [hx, one_mul]
      _ = x ^ (2 * k + 1 + 1) := (pow_succ x (2 * k + 1)).symm
      _ = x ^ ((k + 1) * 2) := by rw [show (k + 1) * 2 = 2 * k + 1 + 1 by ring]
  have h2 := hsq (x ^ (k + 1))
  rw [← h] at h2
  exact h2

theorem nonempty_oFrame_of_blockFrame {p a r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {O : Type} [Group O]
    (hsq : ∀ g : O, g ^ 2 ∈ commutator O)
    (F : BlockFrame (Multiplicative (ZMod (p ^ a))) r O) (μ₀ : ℤ)
    (hμ₀ : r = 2 → ¬ (p : ℤ) ∣ μ₀ ^ 2 - 1)
    (hFr : ∀ i : Fin r, r = 2 → ∃ g : O,
      ∀ c, g * F.T c * g⁻¹ = F.T (Function.update c i (c i ^ μ₀)))
    (hsw : ∀ i j : Fin r, i ≠ j → r = 2 → ∃ g ∈ commutator O,
      ∀ c, g * F.T c * g⁻¹ = F.T (c ∘ Equiv.swap i j)) :
    Nonempty (OFrame p (Multiplicative (ZMod (p ^ a))) r (commutator O)) := by
  have hp := (Fact.out : p.Prime)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hTmem : ∀ c : Fin r → Multiplicative (ZMod (p ^ a)), F.T c ∈ commutator O := by
    intro c
    refine mem_commutator_of_odd_pow_eq_one hsq (Odd.pow hodd : Odd (p ^ a)) ?_
    rw [← map_pow, pow_pPow_eq_one_pi, map_one]
  obtain ⟨T, hT⟩ : ∃ T : (Fin r → Multiplicative (ZMod (p ^ a))) →* commutator O,
      ∀ c, (T c : O) = F.T c :=
    ⟨{ toFun := fun c => ⟨F.T c, hTmem c⟩
       map_one' := Subtype.ext (map_one F.T)
       map_mul' := fun x y => Subtype.ext (map_mul F.T x y) }, fun c => rfl⟩
  have hGconj : ∀ (g : O) (hg : g ∈ commutator O) (c d : Fin r → Multiplicative (ZMod (p ^ a))),
      g * F.T c * g⁻¹ = F.T d →
        ((⟨g, hg⟩ : commutator O)) * T c * ((⟨g, hg⟩ : commutator O))⁻¹ = T d := by
    intro g hg c d h
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hT]
    exact h
  refine ⟨⟨T, ?_, ?_, ?_⟩⟩
  ·
    intro c d h
    apply F.T_injective
    have h' := congrArg Subtype.val h
    rw [hT, hT] at h'
    exact h'
  ·
    intro j k hjk
    have hr2 : 2 ≤ r := by
      have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
      have := j.2
      have := k.2
      omega
    by_cases h2 : r = 2
    ·
      obtain ⟨g, hgΩ, hg⟩ := hsw j k hjk h2
      refine ⟨⟨g, hgΩ⟩, Equiv.swap j k, Equiv.swap_apply_left j k, fun c => ?_⟩
      rw [Equiv.swap_inv]
      exact hGconj g hgΩ c _ (hg c)
    ·
      have hcard : ({j, k} : Finset (Fin r)).card < (Finset.univ : Finset (Fin r)).card := by
        rw [Finset.card_pair hjk, Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      obtain ⟨hlj, hlk⟩ := hl
      obtain ⟨τ, hτdef⟩ : ∃ τ : Equiv.Perm (Fin r), τ = Equiv.swap j l * Equiv.swap j k :=
        ⟨_, rfl⟩
      have hτj : τ j = k := by
        rw [hτdef, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm hjk) (Ne.symm hlk)]
      have hcyc : τ.IsThreeCycle := by
        rw [hτdef]
        exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hlj) hjk hlk
      have hτ3 : τ ^ 3 = 1 := by
        have h := pow_orderOf_eq_one τ
        rwa [hcyc.orderOf] at h
      have hSτ : F.S τ ^ 3 = 1 := by rw [← map_pow, hτ3, map_one]
      have hSΩ : F.S τ ∈ commutator O :=
        mem_commutator_of_odd_pow_eq_one hsq (⟨1, by norm_num⟩ : Odd 3) hSτ
      exact ⟨⟨F.S τ, hSΩ⟩, τ, hτj, fun c => hGconj (F.S τ) hSΩ c _ (F.S_conj τ c)⟩
  ·
    intro hr
    by_cases h2 : r = 2
    ·
      obtain ⟨i₀, j₁, hji⟩ : ∃ i₀ j₁ : Fin r, i₀ ≠ j₁ :=
        ⟨⟨0, by omega⟩, ⟨1, by omega⟩, fun h => by simpa using congrArg Fin.val h⟩
      obtain ⟨u, hu⟩ := hFr i₀ h2
      have hD : u * u ∈ commutator O := by
        rw [← pow_two]
        exact hsq u
      refine ⟨⟨u * u, hD⟩, fun k => if k = i₀ then μ₀ ^ 2 else 1, ⟨i₀, j₁, ?_⟩, fun c => ?_⟩
      · show ¬ (p : ℤ) ∣ (if i₀ = i₀ then μ₀ ^ 2 else 1) - (if j₁ = i₀ then μ₀ ^ 2 else 1)
        rw [if_pos rfl, if_neg (Ne.symm hji)]
        exact hμ₀ h2
      · refine hGconj (u * u) hD c _ ?_
        have e2 : u * u * F.T c * (u * u)⁻¹ = u * (u * F.T c * u⁻¹) * u⁻¹ := by group
        rw [e2, hu c, hu (Function.update c i₀ (c i₀ ^ μ₀))]
        congr 1
        funext k
        by_cases hk : k = i₀
        · subst hk
          simp [← zpow_mul, sq]
        · simp [Function.update_of_ne hk, hk]
    ·
      obtain ⟨a₀, b₀, d₀, hab, hda, hdb⟩ : ∃ a₀ b₀ d₀ : Fin r,
          a₀ ≠ b₀ ∧ d₀ ≠ a₀ ∧ d₀ ≠ b₀ :=
        ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
          fun h => by simpa using congrArg Fin.val h,
          fun h => by simpa using congrArg Fin.val h,
          fun h => by simpa using congrArg Fin.val h⟩
      obtain ⟨u, hu⟩ := F.exists_inv a₀
      have hff : ∀ d : Fin r → Multiplicative (ZMod (p ^ a)),
          Function.update (Function.update d a₀ (d a₀)⁻¹) a₀
            ((Function.update d a₀ (d a₀)⁻¹) a₀)⁻¹ = d := by
        intro d
        simp
      have hinv : ∀ d : Fin r → Multiplicative (ZMod (p ^ a)),
          u⁻¹ * F.T d * u = F.T (Function.update d a₀ (d a₀)⁻¹) := by
        intro d
        have h := hu (Function.update d a₀ (d a₀)⁻¹)
        rw [hff] at h
        rw [← h]
        group
      have hA : ∀ c : Fin r → Multiplicative (ZMod (p ^ a)),
          (F.S (Equiv.swap a₀ b₀))⁻¹ * F.T c * F.S (Equiv.swap a₀ b₀)
            = F.T (c ∘ ⇑(Equiv.swap a₀ b₀)) := by
        intro c
        have h := F.S_conj (Equiv.swap a₀ b₀)⁻¹ c
        simp only [map_inv, inv_inv] at h
        exact h
      have hC : ∀ e : Fin r → Multiplicative (ZMod (p ^ a)),
          F.S (Equiv.swap a₀ b₀) * F.T e * (F.S (Equiv.swap a₀ b₀))⁻¹
            = F.T (e ∘ ⇑(Equiv.swap a₀ b₀)) := by
        intro e
        have h := F.S_conj (Equiv.swap a₀ b₀) e
        rw [Equiv.swap_inv] at h
        exact h
      have hD : u * F.S (Equiv.swap a₀ b₀) * u⁻¹ * (F.S (Equiv.swap a₀ b₀))⁻¹ ∈ commutator O := by
        rw [← commutatorElement_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      have key : ∀ c : Fin r → Multiplicative (ZMod (p ^ a)),
          u * F.S (Equiv.swap a₀ b₀) * u⁻¹ * (F.S (Equiv.swap a₀ b₀))⁻¹ * F.T c *
              (u * F.S (Equiv.swap a₀ b₀) * u⁻¹ * (F.S (Equiv.swap a₀ b₀))⁻¹)⁻¹
            = F.T (fun k => c k ^ (if k = a₀ ∨ k = b₀ then (-1 : ℤ) else 1)) := by
        intro c
        have e1 : u * F.S (Equiv.swap a₀ b₀) * u⁻¹ * (F.S (Equiv.swap a₀ b₀))⁻¹ * F.T c *
              (u * F.S (Equiv.swap a₀ b₀) * u⁻¹ * (F.S (Equiv.swap a₀ b₀))⁻¹)⁻¹
            = u * (F.S (Equiv.swap a₀ b₀) * (u⁻¹ * ((F.S (Equiv.swap a₀ b₀))⁻¹ * F.T c *
                F.S (Equiv.swap a₀ b₀)) * u) * (F.S (Equiv.swap a₀ b₀))⁻¹) * u⁻¹ := by
          group
        rw [e1, hA c, hinv, hC, hu]
        congr 1
        funext k
        by_cases hka : k = a₀
        · simp [hka, Function.update_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
            hab, Ne.symm hab]
        by_cases hkb : k = b₀
        · simp [hkb, Function.update_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
            hab, Ne.symm hab, hka]
        · simp [Function.update_apply, Equiv.swap_apply_of_ne_of_ne, hka, hkb]
      refine ⟨⟨_, hD⟩, fun k => if k = a₀ ∨ k = b₀ then (-1 : ℤ) else 1, ⟨a₀, d₀, ?_⟩,
        fun c => ?_⟩
      ·
        show ¬ (p : ℤ) ∣ (if a₀ = a₀ ∨ a₀ = b₀ then (-1 : ℤ) else 1) -
          (if d₀ = a₀ ∨ d₀ = b₀ then (-1 : ℤ) else 1)
        have hA0 : (if a₀ = a₀ ∨ a₀ = b₀ then (-1 : ℤ) else 1) = -1 := by simp
        have hD0 : (if d₀ = a₀ ∨ d₀ = b₀ then (-1 : ℤ) else 1) = 1 := by simp [hda, hdb]
        rw [hA0, hD0]
        intro h
        apply hp2
        have h2' : (p : ℤ) ∣ ((2 : ℕ) : ℤ) := by
          have e : ((2 : ℕ) : ℤ) = -((-1 : ℤ) - 1) := by norm_num
          rw [e]
          exact dvd_neg.2 h
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (Int.natCast_dvd_natCast.1 h2')
      · exact hGconj _ hD c _ (key c)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
