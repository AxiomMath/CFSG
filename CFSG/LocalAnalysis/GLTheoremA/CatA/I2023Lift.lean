module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023Normalizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAb_lift {X L : Subgroup G} (hL : GLAPComponent 3 X L)
    {Ebar : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)} (hE : IsElemAbelian 3 Ebar)
    (hsec : ∀ e ∈ Ebar, ∃ z : ↥X, QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) z = e ∧
      (z : G) ∈ Subgroup.normalizer (L : Set G))
    (x : ↥X) (hx3 : x ^ 3 = 1) (hxE : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x ∈ Ebar) :
    ∃ S : Subgroup ↥X, IsElemAbelian 3 S ∧ x ∈ S ∧ Nat.card S = Nat.card Ebar ∧
      (∀ s ∈ S, (s : G) ∈ Subgroup.normalizer (L : Set G)) ∧
      ∀ e ∈ Ebar, ∃ s ∈ S, QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) s = e := by
  classical
  haveI hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Nn : Subgroup ↥X := GLAPPrimeCore 3 ↥X with hNn
  set π : ↥X →* (↥X ⧸ Nn) := QuotientGroup.mk' Nn with hπ
  set P : Subgroup ↥X := Ebar.comap π with hP
  have hxP : x ∈ P := hxE
  have hcardNn : Nat.Coprime 3 (Nat.card Nn) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥X
  have hnd : ¬ 3 ∣ Nat.card Nn := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcardNn
  have hEp : IsPGroup 3 Ebar := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g.1 g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hEp
  have hcardP : Nat.card P = Nat.card Nn * Nat.card Ebar :=
    QuotientGroup.card_preimage_mk Nn (Ebar : Set (↥X ⧸ Nn))
  have hfacP : (Nat.card P).factorization 3 = k := by
    have hne1 : Nat.card Nn ≠ 0 := Nat.card_pos.ne'
    have hne2 : 3 ^ k ≠ 0 := by positivity
    rw [hcardP, hk, Nat.factorization_mul hne1 hne2]
    simp [Nat.factorization_eq_zero_of_not_dvd hnd, Nat.Prime.factorization_pow Nat.prime_three]
  have hxP3 : IsPGroup 3 (Subgroup.zpowers (⟨x, hxP⟩ : P)) := by
    have hy : (⟨x, hxP⟩ : P) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    obtain ⟨n, hn⟩ : ∃ n, orderOf (⟨x, hxP⟩ : P) = 3 ^ n := by
      rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hy) with h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
    exact IsPGroup.iff_card.2 ⟨n, by rw [Nat.card_zpowers, hn]⟩
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hxP3
  set S : Subgroup ↥X := (Q : Subgroup ↥P).map P.subtype with hS
  have hQcard : Nat.card (Q : Subgroup ↥P) = Nat.card Ebar := by
    have h := Sylow.card_eq_multiplicity Q
    rw [hfacP] at h
    rw [hk]
    exact h
  have hcardS : Nat.card S = Nat.card Ebar := by
    rw [hS, Subgroup.card_map_of_injective P.subtype_injective, hQcard]
  have hSP : ∀ s ∈ S, ∃ q : ↥P, q ∈ (Q : Subgroup ↥P) ∧ (q : ↥X) = s := by
    intro s hs
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hs
    exact ⟨q, hq, rfl⟩
  have hSEbar : ∀ s ∈ S, π s ∈ Ebar := by
    intro s hs
    obtain ⟨q, -, rfl⟩ := hSP s hs
    exact q.2
  have hSpow : ∀ s ∈ S, ∃ m : ℕ, s ^ (3 ^ m) = 1 := by
    intro s hs
    obtain ⟨q, hq, rfl⟩ := hSP s hs
    obtain ⟨m, hm⟩ := Q.isPGroup' ⟨q, hq⟩
    refine ⟨m, ?_⟩
    have h1 : q ^ (3 ^ m) = 1 := by
      have h := congrArg Subtype.val hm
      simpa using h
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hker : ∀ s ∈ S, π s = 1 → s = 1 := by
    intro s hs hπs
    obtain ⟨m, hm⟩ := hSpow s hs
    have hsN : s ∈ Nn := (QuotientGroup.eq_one_iff s).1 hπs
    have h1 : orderOf s ∣ Nat.card Nn := by
      have h := orderOf_dvd_natCard (⟨s, hsN⟩ : Nn)
      rwa [Subgroup.orderOf_mk] at h
    have h2 : orderOf s ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm
    have h3 : orderOf s ∣ Nat.gcd (3 ^ m) (Nat.card Nn) := Nat.dvd_gcd h2 h1
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left m hcardNn), Nat.dvd_one] at h3
    exact orderOf_eq_one_iff.1 h3
  let f : ↥S → ↥Ebar := fun s => ⟨π s.1, hSEbar s.1 s.2⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : π a.1 = π b.1 := congrArg Subtype.val hab
    have h2 : π (a.1⁻¹ * b.1) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : a.1⁻¹ * b.1 = 1 := hker _ (S.mul_mem (S.inv_mem a.2) b.2) h2
    exact Subtype.ext (eq_of_inv_mul_eq_one h3)
  have hfbij : Function.Bijective f :=
    hfinj.bijective_of_nat_card_le (by simpa using hcardS.symm.le)
  have hsurj : ∀ e ∈ Ebar, ∃ s ∈ S, π s = e := by
    intro e he
    obtain ⟨a, ha⟩ := hfbij.2 ⟨e, he⟩
    exact ⟨a.1, a.2, congrArg Subtype.val ha⟩
  have hEcomm : ∀ a b : ↥Ebar, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  have hScomm : ∀ a b : ↥S, a * b = b * a := by
    intro a b
    apply hfinj
    apply Subtype.ext
    show π (a * b).1 = π (b * a).1
    simp only [Subgroup.coe_mul, map_mul]
    exact congrArg Subtype.val (hEcomm ⟨π a.1, hSEbar a.1 a.2⟩ ⟨π b.1, hSEbar b.1 b.2⟩)
  have hSexp : ∀ s ∈ S, s ^ 3 = 1 := by
    intro s hs
    have h : f (⟨s, hs⟩ ^ 3) = f 1 := by
      apply Subtype.ext
      show π (⟨s, hs⟩ ^ 3 : ↥S).1 = π (1 : ↥S).1
      simp only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one]
      exact hE.2 _ (hSEbar s hs)
    have h' := hfinj h
    exact congrArg Subtype.val h'
  have hnorm : ∀ s ∈ S, (s : G) ∈ Subgroup.normalizer (L : Set G) := by
    intro s hs
    obtain ⟨z, hzπ, hzN⟩ := hsec (π s) (hSEbar s hs)
    have hw1 : π (z⁻¹ * s) = 1 := by
      rw [map_mul, map_inv, hzπ, inv_mul_cancel]
    have hw : z⁻¹ * s ∈ Nn := (QuotientGroup.eq_one_iff _).1 hw1
    have hwG : ((z⁻¹ * s : ↥X) : G) ∈ Subgroup.normalizer (L : Set G) :=
      glaPPrimeCoreOf_le_normalizer_of_component hL (Subgroup.mem_map.2 ⟨z⁻¹ * s, hw, rfl⟩)
    have hsG : (s : G) = (z : G) * ((z⁻¹ * s : ↥X) : G) := by simp
    rw [hsG]
    exact Subgroup.mul_mem _ hzN hwG
  refine ⟨S, ⟨⟨⟨fun a b => hScomm a b⟩⟩, fun s hs => hSexp s hs⟩, ?_, hcardS, hnorm, hsurj⟩
  exact Subgroup.mem_map.2 ⟨⟨x, hxP⟩, hQ (Subgroup.mem_zpowers _), rfl⟩

end CFSG.LocalAnalysis.GLTheoremA

end
