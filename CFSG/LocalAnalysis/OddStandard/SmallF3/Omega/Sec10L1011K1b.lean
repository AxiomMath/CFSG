module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011K1

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {A : Type} [Group A] [Finite A] {B : Subgroup A} {t : A} {K : Subgroup (MulAut A)}
  {φ : (Fin 5 → ZMod 2) → A}

private instance instDecidableIsEvenVec5b (v : Fin 5 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private lemma sec1011_alpha_wfour_nonzero (h : Sec1011A1 B t K φ) (α : ↥K) :
    ∃ w, IsEvenVec w ∧ w ≠ 0 ∧ φ w = (α : MulAut A) (φ (sec1011_wfour 0)) := by
  have hv0 : IsEvenVec (sec1011_wfour 0) := sec1011_wfour_even 0
  have hB : (α : MulAut A) (φ (sec1011_wfour 0)) ∈ B :=
    h.core.B_inv α α.2 _ (h.core.mem hv0)
  obtain ⟨w, hw, hφw⟩ :=
    (h.core.mem_B ((α : MulAut A) (φ (sec1011_wfour 0)))).1 hB
  refine ⟨w, hw, ?_, hφw⟩
  intro hw0
  have hz1 : φ (sec1011_wfour 0) = 1 := by
    have h1 : (α : MulAut A) (φ (sec1011_wfour 0)) = 1 := by
      rw [← hφw, hw0, h.core.map_zero]
    have h2' : (α : MulAut A).symm ((α : MulAut A) (φ (sec1011_wfour 0))) =
        (α : MulAut A).symm 1 := congrArg (fun x => (α : MulAut A).symm x) h1
    simpa using h2'
  exact h.core.ne_one hv0 (sec1011_wfour_ne_zero' 0) hz1

private lemma sec1011_orbit_nonzero_even (h : Sec1011A1 B t K φ) (α : ↥K)
    (w : Fin 5 → ZMod 2) (hw : IsEvenVec w) (hwt : vecWeight w = 2)
    (hφw : φ w = (α : MulAut A) (φ (sec1011_wfour 0))) :
    (MulAction.orbit ↥K (φ (sec1011_wfour 0)) : Set A) =
      {a | ∃ u, IsEvenVec u ∧ u ≠ 0 ∧ a = φ u} := by
  have hv0 : IsEvenVec (sec1011_wfour 0) := sec1011_wfour_even 0
  have hw0wt : vecWeight (sec1011_wfour 0) = 4 := sec1011_wfour_weight 0
  let P : (Fin 5 → ZMod 2) → Prop := fun u =>
    IsEvenVec u ∧ u ≠ 0 ∧ φ u ∈ (MulAction.orbit ↥K (φ (sec1011_wfour 0)) : Set A)
  have hPstab : ∀ σ ∈ alternatingGroup (Fin 5), ∀ u, P u → P (permVec σ u) := by
    intro σ hσ u hu
    obtain ⟨hu_even, hu0, hφu⟩ := hu
    obtain ⟨n, hnK, _, hn⟩ := h.core.N_act σ hσ
    refine ⟨isEvenVec_permVec σ hu_even, ?_, ?_⟩
    · intro h0
      have h1 : u = 0 := by
        calc u = permVec (σ.symm * σ) u := by
              rw [show σ.symm * σ = 1 by exact inv_mul_cancel σ, permVec_one]
          _ = permVec σ.symm (permVec σ u) := permVec_mul σ.symm σ u
          _ = permVec σ.symm 0 := by rw [h0]
          _ = 0 := by ext x; simp [permVec]
      exact hu0 h1
    · rw [← hn u hu_even]
      obtain ⟨m, hmz⟩ := (MulAction.mem_orbit_iff).1 hφu
      have hmz' : (m : MulAut A) (φ (sec1011_wfour 0)) = φ u := by
        simpa [Subgroup.smul_def, MulAut.smul_def] using hmz
      let nm : ↥K := ⟨n * (m : MulAut A), K.mul_mem hnK m.2⟩
      refine (MulAction.mem_orbit_iff).2 ⟨nm, ?_⟩
      change (n * (m : MulAut A)) (φ (sec1011_wfour 0)) = n (φ u)
      rw [MulAut.mul_apply, hmz']
  have hP0 : P (sec1011_wfour 0) :=
    ⟨hv0, sec1011_wfour_ne_zero' 0,
      show φ (sec1011_wfour 0) ∈ _ from
        MulAction.mem_orbit (φ (sec1011_wfour 0)) (1 : ↥K)⟩
  have hPw : P w := by
    refine ⟨hw, ?_, ?_⟩
    · obtain ⟨u', hu', hu'0, hφu'⟩ := sec1011_alpha_wfour_nonzero h α
      have huw : u' = w := h.core.inj u' w hu' hw (hφu'.trans hφw.symm)
      rw [← huw]
      exact hu'0
    · rw [hφw]
      exact MulAction.mem_orbit (φ (sec1011_wfour 0)) α
  have hPall : ∀ u, IsEvenVec u → u ≠ 0 → P u := by
    intro u hu hu0
    rcases even_weight_cases_five u hu with h0 | h2u | h4u
    · exact absurd h0 hu0
    · obtain ⟨σ, hσ, hσu⟩ := sec1011_alt_weight_two w u hwt h2u
      rw [← hσu]
      exact hPstab σ hσ w hPw
    · obtain ⟨σ, hσ, hσu⟩ :=
        exists_alt_permVec_weight_four (sec1011_wfour 0) u hw0wt h4u
      rw [← hσu]
      exact hPstab σ hσ (sec1011_wfour 0) hP0
  have hsub : (MulAction.orbit ↥K (φ (sec1011_wfour 0)) : Set A) ⊆
      {a | ∃ u, IsEvenVec u ∧ u ≠ 0 ∧ a = φ u} := by
    intro a ha
    obtain ⟨β, hβ⟩ := (MulAction.mem_orbit_iff).1 ha
    obtain ⟨u, hu, hu0, hφu⟩ := sec1011_alpha_wfour_nonzero h β
    exact ⟨u, hu, hu0, (hφu.trans hβ).symm⟩
  apply Set.Subset.antisymm hsub
  rintro a ⟨u, hu, hu0, rfl⟩
  exact (hPall u hu hu0).2.2

private lemma sec1011_card_orbit_of_eq (h : Sec1011A1 B t K φ)
    (hset : (MulAction.orbit ↥K (φ (sec1011_wfour 0)) : Set A) =
      {a | ∃ u, IsEvenVec u ∧ u ≠ 0 ∧ a = φ u}) :
    Nat.card (MulAction.orbit ↥K (φ (sec1011_wfour 0))) = 15 := by
  have hset_iff : ∀ a : A, a ∈ (MulAction.orbit ↥K (φ (sec1011_wfour 0)) : Set A) ↔
      ∃ u, IsEvenVec u ∧ u ≠ 0 ∧ a = φ u := by
    intro a
    rw [hset]
    rfl
  let e : {u : Fin 5 → ZMod 2 // IsEvenVec u ∧ u ≠ 0} →
      MulAction.orbit ↥K (φ (sec1011_wfour 0)) :=
    fun u => ⟨φ u.1, (hset_iff (φ u.1)).2 ⟨u.1, u.2.1, u.2.2, rfl⟩⟩
  have hbij : Function.Bijective e := by
    constructor
    · intro u v huv
      apply Subtype.ext
      exact h.core.inj u.1 v.1 u.2.1 v.2.1 (congrArg Subtype.val huv)
    · intro b
      obtain ⟨u, hu, hu0, hbu⟩ := (hset_iff b.1).1 b.2
      exact ⟨⟨u, hu, hu0⟩, Subtype.ext hbu.symm⟩
  have hc := Nat.card_congr (Equiv.ofBijective e hbij)
  rw [← hc, Nat.card_eq_fintype_card]
  decide +kernel

theorem Sec1011A1.W4_stable (h : Sec1011A1 B t K φ) :
    ∀ α ∈ K, ∀ i : Fin 5, ∃ j : Fin 5, α (φ (sec1011_wfour i)) = φ (sec1011_wfour j) := by
  have hnot3 : ¬ (3 : ℕ) ∣ Nat.card (MulAction.orbit ↥K (φ (sec1011_wfour 0))) := by
    obtain ⟨n, hnK, hnne, hn3, hnfix⟩ :=
      h.exists_three (sec1011_wfour_even 0) (sec1011_wfour_weight 0)
    let n' : ↥K := ⟨n, hnK⟩
    have hn'3 : n' ^ 3 = 1 := by
      apply Subtype.ext
      change n ^ 3 = 1
      exact hn3
    have hn'ne : n' ≠ 1 := by
      intro hh
      have h1 : (n' : MulAut A) = 1 := by rw [hh]; rfl
      exact hnne (by simpa [n'] using h1)
    have hn'stab : n' ∈ MulAction.stabilizer ↥K (φ (sec1011_wfour 0)) := by
      rw [MulAction.mem_stabilizer_iff]
      change n (φ (sec1011_wfour 0)) = φ (sec1011_wfour 0)
      exact hnfix
    have h3dvd : 3 ∣ Nat.card (MulAction.stabilizer ↥K (φ (sec1011_wfour 0))) := by
      have ho : orderOf n' = 3 := orderOf_eq_prime hn'3 hn'ne
      rw [← ho]
      exact Subgroup.orderOf_dvd_natCard _ hn'stab
    intro h3orb
    have hOS := sec1011_card_orbit_mul_card_stabilizer (G := ↥K) (φ (sec1011_wfour 0))
    have h9 : 9 ∣ Nat.card ↥K := by
      rw [← hOS]
      simpa using mul_dvd_mul h3orb h3dvd
    rcases h.card_K_cases with hK | hK <;> rw [hK] at h9 <;> norm_num at h9
  have hstep2 : ∀ α ∈ K, ∃ w, IsEvenVec w ∧ vecWeight w = 4 ∧
      φ w = (α : MulAut A) (φ (sec1011_wfour 0)) := by
    intro α hαK
    obtain ⟨w, hw, hw0, hφw⟩ := sec1011_alpha_wfour_nonzero h ⟨α, hαK⟩
    rcases even_weight_cases_five w hw with hzero | htwo | hfour
    · exact absurd hzero hw0
    · exfalso
      have hset := sec1011_orbit_nonzero_even h ⟨α, hαK⟩ w hw htwo hφw
      have hcard := sec1011_card_orbit_of_eq h hset
      exact hnot3 (by rw [hcard]; norm_num)
    · exact ⟨w, hw, hfour, hφw⟩
  intro α hαK i
  obtain ⟨σ, hσ, hσi⟩ :=
    exists_alt_permVec_weight_four (sec1011_wfour 0) (sec1011_wfour i)
      (sec1011_wfour_weight 0) (sec1011_wfour_weight i)
  obtain ⟨n, hnK, _, hn⟩ := h.core.N_act σ hσ
  have hnz : n (φ (sec1011_wfour 0)) = φ (sec1011_wfour i) := by
    rw [hn (sec1011_wfour 0) (sec1011_wfour_even 0), hσi]
  obtain ⟨w, hw, hw4, hφw⟩ := hstep2 (α * n) (K.mul_mem hαK hnK)
  obtain ⟨j, rfl⟩ := sec1011_exists_wfour w hw4
  refine ⟨j, ?_⟩
  rw [hφw, MulAut.mul_apply, hnz]

private noncomputable def sec1011_theta (h : Sec1011A1 B t K φ) (α : ↥K) :
    Equiv.Perm (Fin 5) :=
  let f : Fin 5 → Fin 5 := fun i => Classical.choose (h.W4_stable α α.2 i)
  have hf : Function.Injective f := by
    intro i j hij
    have hi := Classical.choose_spec (h.W4_stable α α.2 i)
    have hj := Classical.choose_spec (h.W4_stable α α.2 j)
    rw [← sec1011_wfour_injective.eq_iff]
    apply h.core.inj _ _ (sec1011_wfour_even _) (sec1011_wfour_even _)
    apply (α : MulAut A).injective
    rw [hi, hj]
    exact congrArg (fun k => φ (sec1011_wfour k)) hij
  Equiv.ofBijective f ⟨hf, (Finite.injective_iff_surjective).mp hf⟩

private lemma sec1011_theta_spec (h : Sec1011A1 B t K φ) (α : ↥K) (i : Fin 5) :
    (α : MulAut A) (φ (sec1011_wfour i)) =
      φ (sec1011_wfour ((sec1011_theta h α) i)) :=
  Classical.choose_spec (h.W4_stable α α.2 i)

private noncomputable def sec1011_thetaHom (h : Sec1011A1 B t K φ) :
    ↥K →* Equiv.Perm (Fin 5) where
  toFun := sec1011_theta h
  map_one' := by
    apply Equiv.ext
    intro i
    have hw : sec1011_wfour ((sec1011_theta h 1) i) =
        sec1011_wfour ((1 : Equiv.Perm (Fin 5)) i) := by
      apply h.core.inj _ _ (sec1011_wfour_even _) (sec1011_wfour_even _)
      rw [← sec1011_theta_spec h 1 i]
      simp
    exact sec1011_wfour_injective hw
  map_mul' := by
    intro α β
    apply Equiv.ext
    intro i
    have hw : sec1011_wfour ((sec1011_theta h (α * β)) i) =
        sec1011_wfour ((sec1011_theta h α * sec1011_theta h β) i) := by
      apply h.core.inj _ _ (sec1011_wfour_even _) (sec1011_wfour_even _)
      calc φ (sec1011_wfour ((sec1011_theta h (α * β)) i))
          = (α * β : MulAut A) (φ (sec1011_wfour i)) :=
              (sec1011_theta_spec h (α * β) i).symm
        _ = (α : MulAut A) ((β : MulAut A) (φ (sec1011_wfour i))) := rfl
        _ = (α : MulAut A) (φ (sec1011_wfour ((sec1011_theta h β) i))) := by
              rw [sec1011_theta_spec h β i]
        _ = φ (sec1011_wfour ((sec1011_theta h α) ((sec1011_theta h β) i))) :=
              sec1011_theta_spec h α ((sec1011_theta h β) i)
        _ = φ (sec1011_wfour ((sec1011_theta h α * sec1011_theta h β) i)) :=
              congrArg (fun k => φ (sec1011_wfour k))
                (Equiv.Perm.mul_apply (sec1011_theta h α) (sec1011_theta h β) i).symm
    exact sec1011_wfour_injective hw

theorem Sec1011A1.card_K_le (h : Sec1011A1 B t K φ) :
    Nat.card ↥K ≤ 120 * Nat.card ↥(sec1011_KB B K) := by
  have hKBle : sec1011_KB B K ≤ K := fun α hα => hα.1
  have hker_le : (sec1011_thetaHom h).ker ≤ (sec1011_KB B K).subgroupOf K := by
    intro α hα
    rw [Subgroup.mem_subgroupOf]
    refine ⟨α.2, ?_⟩
    have hα1 : sec1011_theta h α = 1 := by
      have := MonoidHom.mem_ker.1 hα
      simpa [sec1011_thetaHom] using this
    refine h.core.fixB_of_fixW4 (α : MulAut A) (fun i => ?_)
    calc (α : MulAut A) (φ (sec1011_wfour i))
        = φ (sec1011_wfour ((sec1011_theta h α) i)) := sec1011_theta_spec h α i
      _ = φ (sec1011_wfour ((1 : Equiv.Perm (Fin 5)) i)) := by rw [hα1]
      _ = φ (sec1011_wfour i) := by simp
  have hker_card : Nat.card ↥((sec1011_thetaHom h).ker) ≤ Nat.card ↥(sec1011_KB B K) := by
    calc Nat.card ↥((sec1011_thetaHom h).ker)
        ≤ Nat.card ↥((sec1011_KB B K).subgroupOf K) := Subgroup.card_le_of_le hker_le
      _ = Nat.card ↥(sec1011_KB B K) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKBle)
  have hrange : Nat.card ↥((sec1011_thetaHom h).range) ≤ 120 := by
    have h := Subgroup.card_le_card_group (H := (sec1011_thetaHom h).range)
      (G := Equiv.Perm (Fin 5))
    rw [sec1011_card_perm_five] at h
    exact h
  have hK := Subgroup.card_ker_mul_card_range (sec1011_thetaHom h)
  calc Nat.card ↥K = Nat.card ↥((sec1011_thetaHom h).ker) *
        Nat.card ↥((sec1011_thetaHom h).range) := hK.symm
    _ ≤ Nat.card ↥(sec1011_KB B K) * 120 := Nat.mul_le_mul hker_card hrange
    _ = 120 * Nat.card ↥(sec1011_KB B K) := by ring

end CFSG.OddStandard.SmallF3.Omega
