module

public import CFSG.GH74.GLS.C3.Layer1.BkD6Stmt
public import CFSG.GH74.GLS.C3.Layer1.BkA6K
public import CFSG.GH74.GLS.C3.Layer1.BkXuLift
public import CFSG.GH74.GLS.C3.Layer1.BkL27K

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back

theorem b_prop43c_six_of_42c (h42 : B_L42c_six) : B_prop43c_six := by
  intro G _ _ hG x K M T Q hh p91 he6 hTS hInv
  obtain ⟨e0⟩ := he6
  refine ⟨e0, ?_⟩
  have hcl : T ≤ Subgroup.closure {u : G | u ∈ T ∧ u * u = 1} :=
    h42 G hG x K M T Q hh p91 ⟨e0⟩ hTS hInv
  have hTM : T ≤ M := hh.a.sylowTM.le
  have hcls : ∀ g ∈ Subgroup.closure {u : G | u ∈ T ∧ u * u = 1},
      ∃ hg : g ∈ M, ∃ σ : Equiv.Perm (Fin 6),
        MulAut.congr e0 (Back.actHom hh.a.L_normal.2 ⟨g, hg⟩) =
          MulAut.conjNormal (H := alternatingGroup (Fin 6)) σ := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem u hu =>
      obtain ⟨σ, hσ⟩ := hInv u hu.1 hu.2 e0
      exact ⟨hTM hu.1, σ, hσ⟩
    | one =>
      refine ⟨M.one_mem, 1, ?_⟩
      have : (⟨1, M.one_mem⟩ : ↥M) = 1 := rfl
      rw [this, map_one, map_one, map_one]
    | mul a b _ _ ha hb =>
      obtain ⟨haM, σa, ha⟩ := ha
      obtain ⟨hbM, σb, hb⟩ := hb
      refine ⟨M.mul_mem haM hbM, σa * σb, ?_⟩
      have : (⟨a * b, M.mul_mem haM hbM⟩ : ↥M) = ⟨a, haM⟩ * ⟨b, hbM⟩ := rfl
      rw [this, map_mul, map_mul, ha, hb, map_mul]
    | inv a _ ha =>
      obtain ⟨haM, σa, ha⟩ := ha
      refine ⟨M.inv_mem haM, σa⁻¹, ?_⟩
      have : (⟨a⁻¹, M.inv_mem haM⟩ : ↥M) = (⟨a, haM⟩ : ↥M)⁻¹ := rfl
      rw [this, map_inv, map_inv, ha, map_inv]
  intro t ht
  obtain ⟨_, σ, hσ⟩ := hcls t (hcl ht)
  exact ⟨σ, hσ⟩

theorem b_lemma113_d6_of (ha : B_lemma113a) (h43 : B_prop43c_six) : B_lemma113_d6 := by
  intro G _ _ hG x K L M T Q hh p91 hKL he6
  subst hKL
  obtain ⟨e0⟩ := he6
  have h360 : Nat.card (kBar K) = 360 := by
    rw [Nat.card_congr e0.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hnoV2 : ¬ ∃ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K' := by
    intro hex
    rcases p91.2.2.2 hex with h5 | h7
    · have := card_eq_of_hasL2Model_five h5
      omega
    · obtain ⟨e⟩ := h7
      have h2520 : Nat.card (kBar K) = 2520 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      omega
  have hnot7 : ¬ HasL2Model (kBar K) (fun r => r = 7) := fun h => by
    have := card_eq_of_hasL2Model_seven h
    omega
  have hTS : ¬ IsSylowOf 2 T ⊤ := ha G hG x K K M T Q hh p91 hnot7
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimple : IsSimpleGroup (kBar K) := e0.isSimpleGroup
  have hL34 : ¬ IsL34Quotient (kBar K) :=
    not_isL34Quotient_of_card_lt (by rw [h360]; norm_num)
  have hLn := hh.a.L_normal.2
  have hTM : T ≤ M := hh.a.sylowTM.le
  have hInv : ∀ (u : G) (hu : u ∈ T), u * u = 1 → ∀ e : kBar K ≃* alternatingGroup (Fin 6),
      ∃ σ : Equiv.Perm (Fin 6),
        MulAut.congr e (Back.actHom hh.a.L_normal.2
          ⟨u, hh.a.centralizer_le (hh.a.sylowT.le hu)⟩) =
          MulAut.conjNormal (H := alternatingGroup (Fin 6)) σ := by
    intro u hu hu2 e
    have huC : u ∈ centralizer ({x} : Set G) := hh.a.sylowT.le hu
    have huM : u ∈ M := hh.a.centralizer_le huC
    by_cases hu1 : u = 1
    · subst hu1
      refine ⟨1, ?_⟩
      have : (⟨1, huM⟩ : ↥M) = 1 := rfl
      rw [this, map_one, map_one, map_one]
    · have hu2' : orderOf u = 2 := orderOf_eq_prime (by rwa [sq]) hu1
      have hρ2 : (Back.actHom hLn ⟨u, huM⟩) ^ 2 = 1 := by
        rw [← map_pow]
        have : (⟨u, huM⟩ : ↥M) ^ 2 = 1 := by
          apply Subtype.ext
          simp only [Subgroup.coe_pow, Subgroup.coe_one]
          rw [← hu2']
          exact pow_orderOf_eq_one u
        rw [this, map_one]
      rcases alt6_involution_cases e hρ2 with h | ⟨h3, hodd⟩
      · exact h
      · exfalso
        have hne : IVK.xu (Back.actHom hLn ⟨u, huM⟩) ≠ ⊥ := by
          intro h
          rw [h, Subgroup.card_bot] at h3
          omega
        exact hnoV2 ⟨x, u, K, isV2Triple_of_xu hh.a hsimple hL34 huC hu2' ⟨hne, hodd⟩⟩
  obtain ⟨e1, hT1⟩ := h43 G hG x K M T Q hh p91 ⟨e0⟩ hTS hInv
  let Sig : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
    (MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
      Equiv.Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range
  let Φ : ↥M →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr e1).toMonoidHom.comp (Back.actHom hLn)
  have hNT : T.subgroupOf M ≤ Sig.comap Φ := by
    intro t ht
    rw [Subgroup.mem_subgroupOf] at ht
    obtain ⟨σ, hσ⟩ := hT1 t ht
    exact ⟨σ, hσ.symm⟩
  have hSigIdx := index_conjNormal_range_alt6
  have hSigN : Sig.Normal := Subgroup.normal_of_index_eq_two hSigIdx
  have hidx : (Sig.comap Φ).index ∣ 2 := by
    rw [Subgroup.index_comap]
    exact hSigIdx ▸ Subgroup.relIndex_dvd_index_of_normal Sig Φ.range
  have hodd : Odd (Sig.comap Φ).index := by
    by_contra hev
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
    have h1 : Nat.card ↥(T.subgroupOf M) ∣ Nat.card ↥(Sig.comap Φ) :=
      Subgroup.card_dvd_of_le hNT
    have h2 : Nat.card ↥(T.subgroupOf M) = 2 ^ (Nat.card ↥M).factorization 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv]
      exact hh.a.sylowTM.card_eq
    have h3 := Subgroup.card_mul_index (Sig.comap Φ)
    have h4 : 2 ^ ((Nat.card ↥M).factorization 2 + 1) ∣ Nat.card ↥M := by
      have h5 : 2 ^ (Nat.card ↥M).factorization 2 ∣ Nat.card ↥(Sig.comap Φ) := h2 ▸ h1
      calc 2 ^ ((Nat.card ↥M).factorization 2 + 1)
          = 2 ^ (Nat.card ↥M).factorization 2 * 2 := pow_succ _ _
        _ ∣ Nat.card ↥(Sig.comap Φ) * (Sig.comap Φ).index := Nat.mul_dvd_mul h5 hev
        _ = Nat.card ↥M := h3
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Nat.prime_two h4
  have hN : Sig.comap Φ = ⊤ := by
    rw [← Subgroup.index_eq_one]
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have hΦall : ∀ m : ↥M, Φ m ∈ Sig := fun m => (Subgroup.eq_top_iff' _).1 hN m
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
  let c : Equiv.Perm (Fin 6) ≃* Sig := MonoidHom.ofInjective hinj
  let Φ' : ↥M →* Sig := Φ.codRestrict Sig hΦall
  refine ⟨c.symm.toMonoidHom.comp Φ', ?_⟩
  rw [← Back.actHom_ker hLn]
  ext m
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  show c.symm (Φ' m) = 1 ↔ Back.actHom hLn m = 1
  rw [map_eq_one_iff c.symm c.symm.injective]
  constructor
  · intro h
    have h1 : Φ m = 1 := congrArg Subtype.val h
    exact (map_eq_one_iff _ (MulAut.congr e1).injective).1 h1
  · intro h
    apply Subtype.ext
    show (MulAut.congr e1) (Back.actHom hLn m) = 1
    rw [h, map_one]

end CFSG.GH74.GLS.C3.Layer1.Bk
