module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTypes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement

theorem exists_perfect_map_eq' {A B : Type*} [Group A] [Finite A] [Group B] (f : A →* B)
    {R : Subgroup B} (hR : R ≤ f.range) (hP : ⁅R, R⁆ = R) :
    ∃ N : Subgroup A, ⁅N, N⁆ = N ∧ N.map f = R := by
  classical
  have hne : ∃ n, ∃ N : Subgroup A, N.map f = R ∧ Nat.card N = n :=
    ⟨_, R.comap f, by rw [Subgroup.map_comap_eq, inf_eq_right.2 hR], rfl⟩
  obtain ⟨N, hNmap, hNcard⟩ := Nat.find_spec hne
  refine ⟨N, ?_, hNmap⟩
  have h1 : ⁅N, N⁆ ≤ N := by
    simpa only [sup_idem] using Subgroup.commutator_le_sup N N
  have hmin : Nat.find hne ≤ Nat.card ↥⁅N, N⁆ :=
    Nat.find_min' hne ⟨⁅N, N⁆, by rw [Subgroup.map_commutator, hNmap, hP], rfl⟩
  rw [← hNcard] at hmin
  exact Subgroup.eq_of_le_of_card_ge h1 hmin

@[expose] def BlockOK {G : Type*} [Group G] (H S : Subgroup G) : Prop :=
  ∀ g ∈ H, (∀ s ∈ S, g * s * g⁻¹ ∈ S) → ∀ k : ℕ,
    (∀ s ∈ S, g ^ (3 ^ k) * s * (g ^ (3 ^ k))⁻¹ = s) →
    (∃ p ∈ S, ∀ s ∈ S, g * s * g⁻¹ = p * s * p⁻¹) ∨
      ∃ E : Subgroup G, E ≤ S ∧ IsElemAbelian 3 E ∧ Nat.card E = 9

theorem map_perfectJoin_le {Q : Type*} [Group Q] (φ : MulAut Q) :
    (perfectJoin (⊤ : Subgroup Q)).map φ.toMonoidHom ≤ perfectJoin (⊤ : Subgroup Q) :=
  le_perfectJoin le_top (by rw [← Subgroup.map_commutator, perfectJoin_perfect])

theorem beta_pow_apply {Q : Type*} [Group Q] {B : Type*} [Group B] (β : Q →* B) (φ : MulAut Q)
    (g : B) (hφ : ∀ x, β (φ x) = g * β x * g⁻¹) (n : ℕ) (x : Q) :
    β ((φ ^ n) x) = g ^ n * β x * (g ^ n)⁻¹ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, hφ, ih, pow_succ']
    group

open Classical in
theorem inner_or_elemAbelian {Q : Type} [Group Q] [Finite Q] {k : ℕ} {G : Fin k → Type}
    [∀ j, Group (G j)] [∀ j, Finite (G j)] (S H : ∀ j, Subgroup (G j)) (β : Q →* ∀ j, G j)
    (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hc : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hqs : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) ∨ Group.IsSolvable ↥(S j))
    (hblock : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → BlockOK (H j) (S j))
    (φ : MulAut Q) (g : ∀ j, G j) (hg : ∀ j, g j ∈ H j)
    (hφ : ∀ x, β (φ x) = g * β x * g⁻¹) (m : ℕ)
    (h3 : ∀ x ∈ perfectJoin (⊤ : Subgroup Q), (φ ^ (3 ^ m)) x = x) :
    (∃ v ∈ perfectJoin (⊤ : Subgroup Q), ∀ w ∈ perfectJoin (⊤ : Subgroup Q),
        φ w * (v * w * v⁻¹)⁻¹ ∈ β.ker) ∨
      ∃ j, ∃ E : Subgroup (G j), E ≤ S j ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
        E.map (MonoidHom.mulSingle G j) ≤ (perfectJoin (⊤ : Subgroup Q)).map β := by
  set V : Subgroup Q := perfectJoin (⊤ : Subgroup Q) with hV
  have hVperf : ⁅V, V⁆ = V := perfectJoin_perfect _
  let Sq : ∀ j, Subgroup (G j) := fun j =>
    if CFSG.Open.IsQuasisimple ↥(S j) then S j else ⊥
  have hSq_qs : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → Sq j = S j := fun j h => by
    simp only [Sq, h, ↓reduceIte]
  have hSq_ns : ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → Sq j = ⊥ := fun j h => by
    simp only [Sq, h, ↓reduceIte]
  have hSq_le : ∀ j, Sq j ≤ S j := fun j => by
    by_cases h : CFSG.Open.IsQuasisimple ↥(S j)
    · rw [hSq_qs j h]
    · rw [hSq_ns j h]; exact bot_le
  have hSq_perf : ∀ j, ⁅Sq j, Sq j⁆ = Sq j := fun j => by
    by_cases h : CFSG.Open.IsQuasisimple ↥(S j)
    · rw [hSq_qs j h]
      have hq := h.1
      have h1 : (⊤ : Subgroup ↥(S j)).map (S j).subtype = S j := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
      calc ⁅S j, S j⁆ = ⁅(⊤ : Subgroup ↥(S j)).map (S j).subtype,
            (⊤ : Subgroup ↥(S j)).map (S j).subtype⁆ := by rw [h1]
        _ = Subgroup.map (S j).subtype ⁅(⊤ : Subgroup ↥(S j)), (⊤ : Subgroup ↥(S j))⁆ :=
          (Subgroup.map_commutator _ _ _).symm
        _ = Subgroup.map (S j).subtype (commutator ↥(S j)) := rfl
        _ = S j := by rw [hq, h1]
    · rw [hSq_ns j h]
      exact Subgroup.commutator_bot_left _ |>.trans rfl
  have hPiPerf : ⁅Subgroup.pi Set.univ Sq, Subgroup.pi Set.univ Sq⁆ =
      Subgroup.pi Set.univ Sq := by
    rw [Subgroup.commutator_pi_pi_of_finite]
    congr 1
    funext j
    exact hSq_perf j
  have hPiS : Subgroup.pi Set.univ Sq ≤ Subgroup.pi Set.univ S := fun x hx =>
    (Subgroup.mem_pi _).2 fun j hj => hSq_le j (((Subgroup.mem_pi _).1 hx) j hj)
  have hmapV : V.map β = Subgroup.pi Set.univ Sq := by
    apply le_antisymm
    · have hperf : ⁅V.map β, V.map β⁆ = V.map β := by
        rw [← Subgroup.map_commutator, hVperf]
      have h1 : V.map β ≤ Subgroup.pi Set.univ S := by
        rw [← hperf]
        exact (Subgroup.commutator_mono (Subgroup.map_le_range β V)
          (Subgroup.map_le_range β V)).trans hc
      intro x hx
      refine (Subgroup.mem_pi _).2 fun j _ => ?_
      by_cases hj : CFSG.Open.IsQuasisimple ↥(S j)
      · rw [hSq_qs j hj]
        exact ((Subgroup.mem_pi _).1 (h1 hx)) j trivial
      · rw [hSq_ns j hj]
        have hsolv : Group.IsSolvable ↥(S j) := by
          rcases hqs j with h | h
          · exact absurd h hj
          · exact h
        have hVj : (V.map β).map (Pi.evalMonoidHom G j) = ⊥ := by
          refine BlockFieldIndex.eq_bot_of_perfect_le
            hsolv ?_ ?_
          · rintro _ ⟨y, hy, rfl⟩
            exact ((Subgroup.mem_pi _).1 (h1 hy)) j trivial
          · rw [← Subgroup.map_commutator, hperf]
        have : x j ∈ (V.map β).map (Pi.evalMonoidHom G j) := ⟨x, hx, rfl⟩
        rw [hVj] at this
        exact this
    · obtain ⟨N, hNperf, hNmap⟩ := exists_perfect_map_eq' β (hPiS.trans hS) hPiPerf
      rw [← hNmap]
      exact Subgroup.map_mono (le_perfectJoin le_top hNperf)
  have hmem : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → ∀ s ∈ S j,
      Pi.mulSingle j s ∈ V.map β := fun j hj s hs => by
    rw [hmapV, Subgroup.mem_pi]
    intro i _
    by_cases hij : i = j
    · subst hij
      rw [Pi.mulSingle_eq_same, hSq_qs i hj]
      exact hs
    · rw [Pi.mulSingle_eq_of_ne hij]
      exact Subgroup.one_mem _
  have hnorm : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → ∀ s ∈ S j, g j * s * (g j)⁻¹ ∈ S j := by
    intro j hj s hs
    obtain ⟨w, hw, hwx⟩ := hmem j hj s hs
    have hφw : φ w ∈ V := map_perfectJoin_le φ ⟨w, hw, rfl⟩
    have h1 : β (φ w) ∈ V.map β := ⟨φ w, hφw, rfl⟩
    rw [hmapV, Subgroup.mem_pi] at h1
    have h2 := h1 j trivial
    rw [hφ, hwx] at h2
    have h3 : (g * Pi.mulSingle j s * g⁻¹) j = g j * s * (g j)⁻¹ := by
      simp [Pi.mul_apply, Pi.inv_apply]
    rw [h3, hSq_qs j hj] at h2
    exact h2
  have hcent : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → ∀ s ∈ S j,
      g j ^ (3 ^ m) * s * (g j ^ (3 ^ m))⁻¹ = s := by
    intro j hj s hs
    obtain ⟨w, hw, hwx⟩ := hmem j hj s hs
    have h1 := beta_pow_apply β φ g hφ (3 ^ m) w
    rw [h3 w hw, hwx] at h1
    have h2 := congrFun h1 j
    have h3' : (g ^ (3 ^ m) * Pi.mulSingle j s * (g ^ (3 ^ m))⁻¹) j =
        g j ^ (3 ^ m) * s * (g j ^ (3 ^ m))⁻¹ := by
      simp [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
    rw [h3', Pi.mulSingle_eq_same] at h2
    exact h2.symm
  by_cases hE : ∃ j, CFSG.Open.IsQuasisimple ↥(S j) ∧
      ∃ E : Subgroup (G j), E ≤ S j ∧ IsElemAbelian 3 E ∧ Nat.card E = 9
  · obtain ⟨j, hj, E, hE1, hE2, hE3⟩ := hE
    refine Or.inr ⟨j, E, hE1, hE2, hE3, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    exact hmem j hj e (hE1 he)
  push Not at hE
  left
  have hall : ∀ j, ∃ p : G j, p ∈ Sq j ∧ (CFSG.Open.IsQuasisimple ↥(S j) →
      ∀ s ∈ S j, g j * s * (g j)⁻¹ = p * s * p⁻¹) := by
    intro j
    by_cases hj : CFSG.Open.IsQuasisimple ↥(S j)
    · rcases hblock j hj (g j) (hg j) (hnorm j hj) m (hcent j hj) with
        ⟨p, hp, hpe⟩ | ⟨E, hE1, hE2, hE3⟩
      · exact ⟨p, by rw [hSq_qs j hj]; exact hp, fun _ => hpe⟩
      · exact (hE j hj E hE1 hE2 hE3).elim
    · exact ⟨1, by rw [hSq_ns j hj]; exact Subgroup.one_mem _, fun h => absurd h hj⟩
  choose p hpSq hpe using hall
  have hpmem : (p : ∀ j, G j) ∈ V.map β := by
    rw [hmapV, Subgroup.mem_pi]
    exact fun j _ => hpSq j
  obtain ⟨v, hv, hvp⟩ := hpmem
  refine ⟨v, hv, fun w hw => ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hvp, hφ]
  rw [mul_inv_eq_one]
  funext j
  have hwβ : β w ∈ Subgroup.pi Set.univ Sq := hmapV ▸ ⟨w, hw, rfl⟩
  have hwj := (Subgroup.mem_pi _).1 hwβ j trivial
  by_cases hj : CFSG.Open.IsQuasisimple ↥(S j)
  · rw [hSq_qs j hj] at hwj
    simp only [Pi.mul_apply, Pi.inv_apply]
    exact hpe j hj (β w j) hwj
  · rw [hSq_ns j hj, Subgroup.mem_bot] at hwj
    simp [Pi.mul_apply, Pi.inv_apply, hwj]

theorem exists_lift_elemAbelian {A B : Type*} [Group A] [Finite A] [Group B] (β : A →* B)
    (h2 : IsPGroup 2 β.ker) {V : Subgroup A} {E : Subgroup B} (hEV : E ≤ V.map β)
    (hE : IsElemAbelian 3 E) :
    ∃ E' : Subgroup A, E' ≤ V ∧ IsElemAbelian 3 E' ∧ Nat.card E' = Nat.card E ∧
      (∀ x ∈ E', β x ∈ E) ∧ ∀ x ∈ E', β x = 1 → x = 1 := by
  classical
  have hE3 : IsPGroup 3 E := CFSG.AGLEmbedding.isPGroup_three_of_isElemAbelian_three hE
  set f : ↥V →* ↥(V.map β) := (β.comp V.subtype).codRestrict (V.map β) fun x => ⟨x, x.2, rfl⟩
    with hf
  have hfs : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  set U₁ : Subgroup ↥(V.map β) := E.subgroupOf (V.map β) with hU₁
  have hU₁3 : IsPGroup 3 U₁ := by
    intro x
    obtain ⟨k, hk⟩ := hE3 ⟨(x : B), x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨U, hUle, hU3, hUm⟩ := CFSG.AGLEmbedding.exists_isPGroup_three_map_eq hfs hU₁3
  set E' : Subgroup A := U.map V.subtype with hE'
  have hUE : ∀ u ∈ U, β (u : A) ∈ E := fun u hu => by
    have := hUle hu
    rw [Subgroup.mem_comap, hU₁, Subgroup.mem_subgroupOf] at this
    exact this
  have hE'E : ∀ x ∈ E', β x ∈ E := by
    rintro _ ⟨u, hu, rfl⟩
    exact hUE u hu
  have hinj : ∀ x ∈ E', β x = 1 → x = 1 := by
    rintro _ ⟨u, hu, rfl⟩ h1
    have hxk : (u : A) ∈ β.ker := h1
    obtain ⟨e, he⟩ := hU3 ⟨u, hu⟩
    have hx2 : u ^ (3 ^ e) = 1 := by simpa using congrArg Subtype.val he
    have hx3 : (u : A) ^ (3 ^ e) = 1 := by simpa using congrArg Subtype.val hx2
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
    have hd1 : orderOf (u : A) ∣ Nat.card β.ker := Subgroup.orderOf_dvd_natCard β.ker hxk
    have hd2 : orderOf (u : A) ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hx3
    have hcop : Nat.Coprime (orderOf (u : A)) (Nat.card β.ker) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd2
      rw [hj, hn]
      exact Nat.Coprime.pow _ _ (by norm_num)
    have := Nat.Coprime.eq_one_of_dvd hcop hd1
    exact orderOf_eq_one_iff.1 this
  refine ⟨E', Subgroup.map_subtype_le _, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_, hE'E,
    hinj⟩
  · have hc := hE.1.is_comm.comm ⟨β a, hE'E a a.2⟩ ⟨β b, hE'E b b.2⟩
    have hc' : β ((a : A) * (b : A) * ((b : A) * (a : A))⁻¹) = 1 := by
      have := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul] at this
      rw [map_mul, map_inv, map_mul, map_mul, this, mul_inv_cancel]
    have := hinj _ (mul_mem (mul_mem a.2 b.2) (inv_mem (mul_mem b.2 a.2))) hc'
    simpa using mul_inv_eq_one.1 this
  · refine hinj _ (pow_mem hx 3) ?_
    rw [map_pow]
    exact hE.2 _ (hE'E x hx)
  · refine Nat.card_congr (Equiv.ofBijective (fun u : E' => (⟨β u, hE'E u u.2⟩ : E)) ⟨?_, ?_⟩)
    · intro a b hab
      have hab' : β (a : A) = β (b : A) := congrArg Subtype.val hab
      have h1 : β ((a : A) * (b : A)⁻¹) = 1 := by
        rw [map_mul, map_inv, hab', mul_inv_cancel]
      have := hinj _ (mul_mem a.2 (inv_mem b.2)) h1
      exact Subtype.ext (mul_inv_eq_one.1 this)
    · rintro ⟨e, he⟩
      have : (⟨e, hEV he⟩ : ↥(V.map β)) ∈ U.map f := by
        rw [hUm]
        exact Subgroup.mem_subgroupOf.2 he
      obtain ⟨u, hu, hue⟩ := this
      exact ⟨⟨(u : A), ⟨u, hu, rfl⟩⟩,
        Subtype.ext (show β (u : A) = e from congrArg Subtype.val hue)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
