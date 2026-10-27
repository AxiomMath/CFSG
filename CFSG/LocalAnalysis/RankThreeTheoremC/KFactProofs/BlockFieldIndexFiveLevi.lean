module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexTransport
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open scoped commutatorElement

theorem exists_isPGroup_map_eq_p {p : ℕ} [Fact p.Prime] {W W₁ : Type*} [Group W] [Group W₁]
    [Finite W] {ρ : W →* W₁} (hρ : Function.Surjective ρ) {U₁ : Subgroup W₁}
    (hU₁ : IsPGroup p U₁) : ∃ U : Subgroup W, U ≤ U₁.comap ρ ∧ IsPGroup p U ∧ U.map ρ = U₁ := by
  set C := U₁.comap ρ
  let ρ' : C →* U₁ := (ρ.comp C.subtype).codRestrict U₁ fun x => x.2
  have hρ' : Function.Surjective ρ' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hρ y
    exact ⟨⟨x, hy⟩, rfl⟩
  have : Finite U₁ := Finite.of_surjective ρ' hρ'
  obtain ⟨P⟩ : Nonempty (Sylow p C) := inferInstance
  have hPtop : ((P : Subgroup C).map ρ') = ⊤ := by
    rw [← Sylow.coe_mapSurjective hρ']
    obtain ⟨n, hn⟩ := hU₁.index ((P.mapSurjective hρ' : Sylow p U₁) : Subgroup U₁)
    have hnd := (P.mapSurjective hρ').not_dvd_index
    rcases n with _ | n
    · exact Subgroup.index_eq_one.1 (by simpa using hn)
    · exact absurd (hn ▸ dvd_pow_self p (Nat.succ_ne_zero n)) hnd
  refine ⟨(P : Subgroup C).map C.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_⟩
  have e : ((P : Subgroup C).map C.subtype).map ρ = ((P : Subgroup C).map ρ').map U₁.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [e, hPtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

@[expose] def BlockOKP (p : ℕ) {G : Type*} [Group G] (H S : Subgroup G) : Prop :=
  ∀ g ∈ H, (∀ s ∈ S, g * s * g⁻¹ ∈ S) → ∀ k : ℕ,
    (∀ s ∈ S, g ^ (p ^ k) * s * (g ^ (p ^ k))⁻¹ = s) →
    (∃ u ∈ S, ∀ s ∈ S, g * s * g⁻¹ = u * s * u⁻¹) ∨
      ∃ E : Subgroup G, E ≤ S ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2

open Classical in
theorem inner_or_elemAbelianP {p : ℕ} {Q : Type} [Group Q] [Finite Q] {k : ℕ} {G : Fin k → Type}
    [∀ j, Group (G j)] [∀ j, Finite (G j)] (S H : ∀ j, Subgroup (G j)) (β : Q →* ∀ j, G j)
    (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hc : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hqs : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) ∨ Group.IsSolvable ↥(S j))
    (hblock : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → BlockOKP p (H j) (S j))
    (φ : MulAut Q) (g : ∀ j, G j) (hg : ∀ j, g j ∈ H j)
    (hφ : ∀ x, β (φ x) = g * β x * g⁻¹) (m : ℕ)
    (h3 : ∀ x ∈ perfectJoin (⊤ : Subgroup Q), (φ ^ (p ^ m)) x = x) :
    (∃ v ∈ perfectJoin (⊤ : Subgroup Q), ∀ w ∈ perfectJoin (⊤ : Subgroup Q),
        φ w * (v * w * v⁻¹)⁻¹ ∈ β.ker) ∨
      ∃ j, ∃ E : Subgroup (G j), E ≤ S j ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
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
      g j ^ (p ^ m) * s * (g j ^ (p ^ m))⁻¹ = s := by
    intro j hj s hs
    obtain ⟨w, hw, hwx⟩ := hmem j hj s hs
    have h1 := beta_pow_apply β φ g hφ (p ^ m) w
    rw [h3 w hw, hwx] at h1
    have h2 := congrFun h1 j
    have h3' : (g ^ (p ^ m) * Pi.mulSingle j s * (g ^ (p ^ m))⁻¹) j =
        g j ^ (p ^ m) * s * (g j ^ (p ^ m))⁻¹ := by
      simp [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
    rw [h3', Pi.mulSingle_eq_same] at h2
    exact h2.symm
  by_cases hE : ∃ j, CFSG.Open.IsQuasisimple ↥(S j) ∧
      ∃ E : Subgroup (G j), E ≤ S j ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2
  · obtain ⟨j, hj, E, hE1, hE2, hE3⟩ := hE
    refine Or.inr ⟨j, E, hE1, hE2, hE3, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    exact hmem j hj e (hE1 he)
  push Not at hE
  left
  have hall : ∀ j, ∃ u : G j, u ∈ Sq j ∧ (CFSG.Open.IsQuasisimple ↥(S j) →
      ∀ s ∈ S j, g j * s * (g j)⁻¹ = u * s * u⁻¹) := by
    intro j
    by_cases hj : CFSG.Open.IsQuasisimple ↥(S j)
    · rcases hblock j hj (g j) (hg j) (hnorm j hj) m (hcent j hj) with
        ⟨u, hu, hpe⟩ | ⟨E, hE1, hE2, hE3⟩
      · exact ⟨u, by rw [hSq_qs j hj]; exact hu, fun _ => hpe⟩
      · exact (hE j hj E hE1 hE2 hE3).elim
    · exact ⟨1, by rw [hSq_ns j hj]; exact Subgroup.one_mem _, fun h => absurd h hj⟩
  choose u hpSq hpe using hall
  have hpmem : (u : ∀ j, G j) ∈ V.map β := by
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

theorem exists_lift_elemAbelianP {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {A B : Type*} [Group A]
    [Finite A] [Group B] (β : A →* B)
    (h2 : IsPGroup 2 β.ker) {V : Subgroup A} {E : Subgroup B} (hEV : E ≤ V.map β)
    (hE : IsElemAbelian p E) :
    ∃ E' : Subgroup A, E' ≤ V ∧ IsElemAbelian p E' ∧ Nat.card E' = Nat.card E ∧
      (∀ x ∈ E', β x ∈ E) ∧ ∀ x ∈ E', β x = 1 → x = 1 := by
  classical
  have hE3 : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE
  set f : ↥V →* ↥(V.map β) := (β.comp V.subtype).codRestrict (V.map β) fun x => ⟨x, x.2, rfl⟩
    with hf
  have hfs : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  set U₁ : Subgroup ↥(V.map β) := E.subgroupOf (V.map β) with hU₁
  have hU₁3 : IsPGroup p U₁ := by
    intro x
    obtain ⟨k, hk⟩ := hE3 ⟨(x : B), x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨U, hUle, hU3, hUm⟩ := exists_isPGroup_map_eq_p hfs hU₁3
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
    have hx2 : u ^ (p ^ e) = 1 := by simpa using congrArg Subtype.val he
    have hx3 : (u : A) ^ (p ^ e) = 1 := by simpa using congrArg Subtype.val hx2
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
    have hd1 : orderOf (u : A) ∣ Nat.card β.ker := Subgroup.orderOf_dvd_natCard β.ker hxk
    have hd2 : orderOf (u : A) ∣ p ^ e := orderOf_dvd_of_pow_eq_one hx3
    have hcop : Nat.Coprime (orderOf (u : A)) (Nat.card β.ker) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hd2
      rw [hj, hn]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).2 hp2)
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
  · refine hinj _ (pow_mem hx p) ?_
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

theorem actsInnerly_of_levi_dataP {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} [L.Normal] (hPL : P ≤ L)
    {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) (Q : Subgroup K) (hQ : Q = coverSub ρ P)
    {k : ℕ} {G : Fin k → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]
    (S H : ∀ j, Subgroup (G j)) (β : ↥Q →* ∀ j, G j)
    (h2 : IsPGroup 2 β.ker) (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hc : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hqs : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) ∨ Group.IsSolvable ↥(S j))
    (hblock : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → BlockOKP p (H j) (S j))
    (hZ : ∀ (j : Fin k) (E : Subgroup (G j)), E ≤ S j → IsElemAbelian p E → Nat.card E = p ^ 2 →
      ∀ x : ↥Q, ρ (x : K) = 1 → β x ∈ E.map (MonoidHom.mulSingle G j) → x = 1)
    (φ : MulAut ↥Q) (g : ∀ j, G j) (hg : ∀ j, g j ∈ H j)
    (hφ : ∀ x, β (φ x) = g * β x * g⁻¹) {a : Y}
    (hcompat : ∀ x : ↥Q,
      (MulAut.conjNormal a : MulAut ↥L) (ρ (x : K)) * (ρ ((φ x : ↥Q) : K))⁻¹ ∈
        Subgroup.center ↥L)
    (hpow : ∃ m : ℕ, ∀ w ∈ perfectJoin P, a ^ (p ^ m) * w = w * a ^ (p ^ m))
    (hrk : Open.pRank p (perfectJoin P) ≤ 1) :
    ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P) := by
  subst hQ
  classical
  obtain ⟨m, hm⟩ := hpow
  have hker₀ := coverHom_ker_le_center ρ hker P
  have hVQperf : ⁅perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)),
      perfectJoin (⊤ : Subgroup ↥(coverSub ρ P))⁆ = perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)) :=
    perfectJoin_perfect _
  have hVQ := map_perfectJoin_coverHomY ρ hρ hker hPL
  have hVQstable : ∀ u ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)),
      φ u ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)) := fun u hu =>
    map_perfectJoin_le φ ⟨u, hu, rfl⟩
  have hVQstableN : ∀ n : ℕ, ∀ u ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)),
      (φ ^ n) u ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)) := by
    intro n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih =>
      intro u hu
      rw [pow_succ', MulAut.mul_apply]
      exact hVQstable _ (ih u hu)
  have h5 : ∀ u ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)),
      (MulAut.conjNormal a : MulAut ↥L) (coverHom ρ P u) = coverHom ρ P (φ u) :=
    eqOn_of_perfect_central ((MulAut.conjNormal a : MulAut ↥L).toMonoidHom.comp (coverHom ρ P))
      ((coverHom ρ P).comp φ.toMonoidHom) hVQperf (fun x _ => hcompat x)
  have h6 : ∀ n : ℕ, ∀ u ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)),
      ((MulAut.conjNormal a : MulAut ↥L) ^ n) (coverHom ρ P u) =
        coverHom ρ P ((φ ^ n) u) := by
    intro n
    induction n with
    | zero => intro u hu; simp
    | succ n ih =>
      intro u hu
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ih u hu]
      exact h5 _ (hVQstableN n u hu)
  have h7 : ∀ x ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)), (φ ^ (p ^ m)) x = x := by
    have hcomm : ∀ x ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)),
        (φ ^ (p ^ m)).toMonoidHom x * (MonoidHom.id ↥(coverSub ρ P) x)⁻¹ ∈
          Subgroup.center ↥(coverSub ρ P) := by
      intro x hx
      apply hker₀
      rw [MonoidHom.mem_ker]
      change coverHom ρ P ((φ ^ (p ^ m)) x * x⁻¹) = 1
      rw [map_mul, map_inv, ← h6 (p ^ m) x hx, ← map_pow]
      have hxw : coverHomY ρ P x ∈ perfectJoin P := hVQ ▸ ⟨x, hx, rfl⟩
      have h8 : (MulAut.conjNormal (a ^ p ^ m) : MulAut ↥L) (coverHom ρ P x) =
          coverHom ρ P x := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        change a ^ p ^ m * coverHomY ρ P x * (a ^ p ^ m)⁻¹ = coverHomY ρ P x
        rw [hm _ hxw]; group
      rw [h8, mul_inv_cancel]
    exact eqOn_of_perfect_central ((φ ^ (p ^ m)).toMonoidHom) (MonoidHom.id _) hVQperf hcomm
  rcases inner_or_elemAbelianP S H β hS hc hqs hblock φ g hg hφ m h7 with
    ⟨v, hv, hvw⟩ | ⟨j, E, hES, hE, hcard, hEV⟩
  · have hvY : coverHomY ρ P v⁻¹ ∈ perfectJoin P :=
      hVQ ▸ ⟨v⁻¹, Subgroup.inv_mem _ hv, rfl⟩
    refine ⟨coverHomY ρ P v⁻¹, hvY, fun w' hw' => ?_⟩
    rw [← hVQ] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    have huV : v⁻¹ * w * v ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) hw) hv
    have h5u : a * coverHomY ρ P (v⁻¹ * w * v) * a⁻¹ =
        coverHomY ρ P (φ (v⁻¹ * w * v)) := by
      have := congrArg (fun z : ↥L => (z : Y)) (h5 _ huV)
      simp only [MulAut.conjNormal_apply] at this
      exact this
    have hmemM : φ (v⁻¹ * w * v) * w⁻¹ ∈ perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)) ⊓ β.ker := by
      refine ⟨Subgroup.mul_mem _ (hVQstable _ huV) (Subgroup.inv_mem _ hw), ?_⟩
      have h9 := hvw _ huV
      have e : v * (v⁻¹ * w * v) * v⁻¹ = w := by group
      rwa [e] at h9
    have hpc : (perfectJoin (⊤ : Subgroup ↥(coverSub ρ P)) ⊓ β.ker).map (coverHomY ρ P) ≤
        pCoreOf 2 (perfectJoin P) := by
      rw [← hVQ]
      refine map_le_pCoreOf (coverHomY ρ P) inf_le_left (fun x hx n hn => ⟨?_, ?_⟩)
        (h2.to_le inf_le_right)
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hn.1) (Subgroup.inv_mem _ hx)
      · show x * n * x⁻¹ ∈ β.ker
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 hn.2,
          mul_one, mul_inv_cancel]
    have hcalc : ⁅a * coverHomY ρ P v⁻¹, coverHomY ρ P w⁆ =
        coverHomY ρ P (φ (v⁻¹ * w * v) * w⁻¹) := by
      calc ⁅a * coverHomY ρ P v⁻¹, coverHomY ρ P w⁆ =
          (a * coverHomY ρ P (v⁻¹ * w * v) * a⁻¹) * (coverHomY ρ P w)⁻¹ := by
            rw [map_mul (coverHomY ρ P), map_mul (coverHomY ρ P), map_inv (coverHomY ρ P),
              commutatorElement_def]; group
        _ = coverHomY ρ P (φ (v⁻¹ * w * v)) * (coverHomY ρ P w)⁻¹ := by rw [h5u]
        _ = coverHomY ρ P (φ (v⁻¹ * w * v) * w⁻¹) := by
            rw [map_mul (coverHomY ρ P), map_inv (coverHomY ρ P)]
    rw [hcalc]
    exact hpc ⟨_, hmemM, rfl⟩
  · exfalso
    have hÊel : IsElemAbelian p (E.map (MonoidHom.mulSingle G j)) :=
      CFSG.SectionRank.isElemAbelian_map hE _
    have hÊcard : Nat.card (E.map (MonoidHom.mulSingle G j)) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (f := MonoidHom.mulSingle G j) (Pi.mulSingle_injective j),
        hcard]
    obtain ⟨E', hE'V, hE'el, hE'card, hE'β, hE'inj⟩ := exists_lift_elemAbelianP hp2 β h2 hEV hÊel
    have hθinj : ∀ x ∈ E', coverHomY ρ P x = 1 → x = 1 := by
      intro x hx h1
      have h2' : ρ (x : K) = 1 := Subtype.ext h1
      exact hZ j E hES hE hcard x h2' (hE'β x hx)
    have hE''V : E'.map (coverHomY ρ P) ≤ perfectJoin P := hVQ ▸ Subgroup.map_mono hE'V
    have hE''el : IsElemAbelian p (E'.map (coverHomY ρ P)) :=
      CFSG.SectionRank.isElemAbelian_map hE'el _
    have hE''card : Nat.card (E'.map (coverHomY ρ P)) = p ^ 2 := by
      have hbij : Function.Bijective (fun x : E' =>
          (⟨coverHomY ρ P x, ⟨x, x.2, rfl⟩⟩ : E'.map (coverHomY ρ P))) := by
        refine ⟨fun x y hxy => ?_, fun y => ?_⟩
        · have h1 : coverHomY ρ P ((x : ↥(coverSub ρ P))⁻¹ * y) = 1 := by
            rw [map_mul, map_inv]
            have := congrArg Subtype.val hxy
            simp only at this
            rw [this, inv_mul_cancel]
          have := hθinj _ (E'.mul_mem (E'.inv_mem x.2) y.2) h1
          exact Subtype.ext (inv_mul_eq_one.1 this)
        · obtain ⟨z, hz, hzy⟩ := y.2
          exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
      rw [← Nat.card_congr (Equiv.ofBijective _ hbij), hE'card, hÊcard]
    have := CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt hE''V hE''el hE''card
    omega

theorem leviInnAt_of_levi_dataP {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} [L.Normal] (hPL : P ≤ L)
    {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) (Q : Subgroup K) (hQ : Q = coverSub ρ P)
    {k : ℕ} {G : Fin k → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]
    (S H : ∀ j, Subgroup (G j)) (β : ↥Q →* ∀ j, G j)
    (h2 : IsPGroup 2 β.ker) (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hc : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hqs : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) ∨ Group.IsSolvable ↥(S j))
    (hH : ∀ (x : ↥Q) (j : Fin k), β x j ∈ H j)
    (hblock : ∀ j, CFSG.Open.IsQuasisimple ↥(S j) → BlockOKP p (H j) (S j))
    (hZ : ∀ (j : Fin k) (E : Subgroup (G j)), E ≤ S j → IsElemAbelian p E → Nat.card E = p ^ 2 →
      ∀ x : ↥Q, ρ (x : K) = 1 → β x ∈ E.map (MonoidHom.mulSingle G j) → x = 1)
    (hrk : Open.pRank p (perfectJoin P) ≤ 1) : LeviInnAtP p P := by
  intro l hl m hcomm
  have hlL : l ∈ L := hPL hl
  obtain ⟨x, hx⟩ := hρ ⟨l, hlL⟩
  have hxQ : x ∈ Q := by
    rw [hQ]
    show ρ x ∈ P.subgroupOf L
    rw [hx]
    exact hl
  set x₀ : ↥Q := ⟨x, hxQ⟩ with hx₀
  refine actsInnerly_of_levi_dataP hp2 hPL ρ hρ hker Q hQ S H β h2 hS hc hqs hblock hZ
    (MulAut.conj x₀) (β x₀) (fun j => hH x₀ j) (fun y => ?_) (a := l) (fun y => ?_)
    ⟨m, fun w hw => ?_⟩ hrk
  · rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  · have h1 : (MulAut.conjNormal l : MulAut ↥L) (ρ (y : K)) = ρ x * ρ (y : K) * (ρ x)⁻¹ := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have := congrArg Subtype.val hx
      simp only at this
      rw [← this]
      rfl
    have h2' : ρ (((MulAut.conj x₀ y : ↥Q) : K)) = ρ x * ρ (y : K) * (ρ x)⁻¹ := by
      rw [MulAut.conj_apply]
      simp [hx₀, map_mul, map_inv]
    rw [h1, h2', mul_inv_cancel]
    exact Subgroup.one_mem _
  · exact (commutatorElement_eq_one_iff_mul_comm.1 (hcomm w hw))


end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
