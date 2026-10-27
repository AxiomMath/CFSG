module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherWalterSchurPairing
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitCentralExtension
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover
public import CFSG.Walter.JRFacts
public import CFSG.Walter.AStar
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.ComponentClassification.WalterSchur

open scoped commutatorElement MatrixGroups

section Transfer

variable {K : Type*} [Group K] [Finite K]

theorem le_commutator_sylow (hK : commutator K = ⊤) (S : Sylow 2 K) {Z : Subgroup K}
    (hZc : Z ≤ Subgroup.center K) (hZ2 : IsPGroup 2 Z) :
    Z ≤ ⁅(S : Subgroup K), (S : Subgroup K)⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := AschbacherToolkit.central_sylow_commutator S hZc hZ2
  rw [hK, inf_top_eq, map_commutator_eq, Subgroup.range_subtype] at h
  rw [h]
  exact inf_le_right

theorem eq_bot_of_sylow_commute (hK : commutator K = ⊤) (S : Sylow 2 K)
    (hS : ∀ a ∈ (S : Subgroup K), ∀ b ∈ (S : Subgroup K), a * b = b * a) {Z : Subgroup K}
    (hZc : Z ≤ Subgroup.center K) (hZ2 : IsPGroup 2 Z) : Z = ⊥ := by
  have h := le_commutator_sylow hK S hZc hZ2
  have hbot : ⁅(S : Subgroup K), (S : Subgroup K)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hS a ha b hb
  rw [hbot] at h
  exact le_bot_iff.mp h

end Transfer

section FourGroup

variable {E : Type*} [Group E] [Finite E]

theorem card_le_two_of_generators (hE : commutator E = ⊤) {K : Subgroup E}
    (hKc : K ≤ Subgroup.center E) (hK2 : IsPGroup 2 K) (P : Sylow 2 E) {x y : E}
    (hx : x ∈ (P : Subgroup E)) (hy : y ∈ (P : Subgroup E)) (hx2 : x * x ∈ K)
    (hgen : (P : Subgroup E) ≤ Subgroup.closure {x, y} ⊔ K)
    (hab : ∀ a ∈ (P : Subgroup E), ∀ b ∈ (P : Subgroup E), ⁅a, b⁆ ∈ K) :
    Nat.card K ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Pg := (P : Subgroup E) with hPgdef
  have hKn : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [(Subgroup.mem_center_iff.mp (hKc hn) g), mul_inv_cancel_right]
    exact hn
  have hKP : K ≤ Pg := hK2.le_sylow_of_normal P
  have hKP' : K ≤ (commutator Pg).map Pg.subtype := by
    rw [map_commutator_eq, Subgroup.range_subtype]
    exact le_commutator_sylow hE P hKc hK2
  set x' : Pg := ⟨x, hx⟩
  set y' : Pg := ⟨y, hy⟩
  set c : Pg := ⁅x', y'⁆ with hcdef
  have hcK : (c : E) ∈ K := hab x hx y hy
  have hcz : ∀ g : Pg, g * c = c * g := by
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hKc hcK) g
  set N : Subgroup Pg := Subgroup.zpowers c with hNdef
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hcomm : Commute g (c ^ j) := Commute.zpow_right (hcz g) j
    rw [hcomm.eq, mul_inv_cancel_right]
    exact hn
  have hKcomm : ∀ s : Pg, (s : E) ∈ K → ∀ t : Pg, ⁅s, t⁆ = 1 := by
    intro s hs t
    rw [commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hKc hs) t).symm
  have hKcomm' : ∀ s t : Pg, (t : E) ∈ K → ⁅s, t⁆ = 1 := by
    intro s t ht
    rw [← commutatorElement_inv, hKcomm t ht s, inv_one]
  set S : Set Pg := {x', y'} ∪ ((K.subgroupOf Pg : Subgroup Pg) : Set Pg) with hSdef
  have hS : Subgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro p _
    have hle : Subgroup.closure {x, y} ⊔ K ≤ (Subgroup.closure S).map Pg.subtype := by
      refine sup_le ?_ ?_
      · rw [Subgroup.closure_le]
        rintro z (rfl | rfl)
        · exact ⟨x', Subgroup.subset_closure (Or.inl (Or.inl rfl)), rfl⟩
        · exact ⟨y', Subgroup.subset_closure (Or.inl (Or.inr rfl)), rfl⟩
      · intro z hz
        exact ⟨⟨z, hKP hz⟩, Subgroup.subset_closure (Or.inr (Subgroup.mem_subgroupOf.mpr hz)),
          rfl⟩
    obtain ⟨q, hq, hqp⟩ := hle (hgen p.2)
    rw [show p = q from Subtype.ext hqp.symm]
    exact hq
  have hc : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ N := by
    have hcN : c ∈ N := Subgroup.mem_zpowers c
    rintro s ((rfl | rfl) | hs) t ((rfl | rfl) | ht)
    · rw [commutatorElement_self]; exact N.one_mem
    · exact hcN
    · rw [hKcomm' _ _ (Subgroup.mem_subgroupOf.mp ht)]; exact N.one_mem
    · rw [← commutatorElement_inv]; exact N.inv_mem hcN
    · rw [commutatorElement_self]; exact N.one_mem
    · rw [hKcomm' _ _ (Subgroup.mem_subgroupOf.mp ht)]; exact N.one_mem
    all_goals rw [hKcomm _ (Subgroup.mem_subgroupOf.mp hs)]; exact N.one_mem
  have hP'N := AschbacherToolkit.commutator_le_of_closure_eq_top N hS hc
  have hle : K ≤ Subgroup.zpowers ⁅x, y⁆ := by
    refine hKP'.trans ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine hP'N.trans ?_
    rw [hNdef, Subgroup.zpowers_le, Subgroup.mem_comap]
    exact Subgroup.mem_zpowers _
  have hsq : ⁅x, y⁆ ^ 2 = 1 := by
    have hxc : Commute x ⁅x, y⁆ := (Subgroup.mem_center_iff.mp (hKc (hab x hx y hy)) x)
    rw [hxc.commutatorElement_pow_left, sq, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hKc hx2) y).symm
  have hord : orderOf ⁅x, y⁆ ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hsq)
  calc Nat.card K ≤ Nat.card (Subgroup.zpowers ⁅x, y⁆) := Subgroup.card_le_of_le hle
    _ = orderOf ⁅x, y⁆ := Nat.card_zpowers _
    _ ≤ 2 := hord

end FourGroup

section Preimage

variable {K : Type*} [Group K] {Z₀ : Subgroup K} [Z₀.Normal]

theorem exists_sylow_comap (hZ2 : IsPGroup 2 Z₀) (P : Sylow 2 (K ⧸ Z₀)) :
    ∃ S : Sylow 2 K, (S : Subgroup K) = (P : Subgroup (K ⧸ Z₀)).comap (QuotientGroup.mk' Z₀) :=
  ⟨P.comapOfKerIsPGroup (QuotientGroup.mk' Z₀) (by rwa [QuotientGroup.ker_mk'])
    (by rw [(QuotientGroup.mk' Z₀).range_eq_top_of_surjective (QuotientGroup.mk'_surjective Z₀)];
        exact le_top), rfl⟩

theorem commutatorElement_mem_of_comap {P : Subgroup (K ⧸ Z₀)}
    (hP : IsMulCommutative P) {a b : K} (ha : a ∈ P.comap (QuotientGroup.mk' Z₀))
    (hb : b ∈ P.comap (QuotientGroup.mk' Z₀)) : ⁅a, b⁆ ∈ Z₀ := by
  rw [← QuotientGroup.ker_mk' Z₀, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact congrArg Subtype.val (hP.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)

end Preimage

section Small

variable {K : Type*} [Group K] [Finite K] {Z₀ : Subgroup K} [Z₀.Normal]

theorem card_le_two_of_card_lt_eight (hKp : commutator K = ⊤) (hZc : Z₀ ≤ Subgroup.center K)
    (hZ2 : IsPGroup 2 Z₀) (P : Sylow 2 (K ⧸ Z₀)) (hP : IsMulCommutative (P : Subgroup (K ⧸ Z₀)))
    (h8 : Nat.card (P : Subgroup (K ⧸ Z₀)) < 8) : Nat.card Z₀ ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_comap hZ2 P
  set π := QuotientGroup.mk' Z₀ with hπ
  have hmemS : ∀ s : K, s ∈ (S : Subgroup K) ↔ π s ∈ (P : Subgroup (K ⧸ Z₀)) := by
    intro s
    rw [hS, Subgroup.mem_comap]
  have hcomm : ∀ a ∈ (S : Subgroup K), ∀ b ∈ (S : Subgroup K), ⁅a, b⁆ ∈ Z₀ := fun a ha b hb =>
    commutatorElement_mem_of_comap hP (hS ▸ ha) (hS ▸ hb)
  have hker : ∀ s : K, π s = 1 → s ∈ Z₀ := fun s hs => by
    rwa [← QuotientGroup.ker_mk' Z₀, MonoidHom.mem_ker]
  by_cases hcyc : IsCyclic (P : Subgroup (K ⧸ Z₀))
  ·
    have hSab : ∀ a ∈ (S : Subgroup K), ∀ b ∈ (S : Subgroup K), a * b = b * a := by
      let f : (S : Subgroup K) →* (P : Subgroup (K ⧸ Z₀)) :=
        (π.comp (S : Subgroup K).subtype).codRestrict _ (fun s => (hmemS s).mp s.2)
      have hf : f.ker ≤ Subgroup.center (S : Subgroup K) := by
        intro s hs
        have hsZ : (s : K) ∈ Z₀ := hker s (congrArg Subtype.val hs)
        rw [Subgroup.mem_center_iff]
        intro t
        exact Subtype.ext (Subgroup.mem_center_iff.mp (hZc hsZ) t)
      intro a ha b hb
      exact congrArg Subtype.val
        ((f.isMulCommutative_of_isCyclic_of_ker_le_center hf).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [eq_bot_of_sylow_commute hKp S hSab hZc hZ2, Subgroup.card_bot]
    norm_num
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp P.isPGroup'
  have hcard4 : Nat.card (P : Subgroup (K ⧸ Z₀)) = 4 := by
    rcases n with _ | _ | _ | n
    · exfalso
      rw [pow_zero] at hn
      have : Subsingleton (P : Subgroup (K ⧸ Z₀)) := (Nat.card_eq_one_iff_unique.mp hn).1
      exact hcyc inferInstance
    · exfalso
      exact hcyc (isCyclic_of_prime_card (p := 2) (by rw [hn, pow_one]))
    · rw [hn]; norm_num
    · exfalso
      rw [hn, pow_succ, pow_succ, pow_succ] at h8
      have := Nat.one_le_two_pow (n := n)
      omega
  have hsq : ∀ p : (P : Subgroup (K ⧸ Z₀)), p * p = 1 := by
    intro p
    have hdvd : orderOf p ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hcard4]
      exact orderOf_dvd_natCard p
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hk2 : k ≠ 2 := by
      rintro rfl
      exact hcyc (isCyclic_of_orderOf_eq_card p (by rw [hk', hcard4]; norm_num))
    have h2 : orderOf p ∣ 2 := by
      rw [hk']
      interval_cases k
      · norm_num
      · norm_num
      · exact absurd rfl hk2
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  have hK4 : IsKleinFour (P : Subgroup (K ⧸ Z₀)) := by
    refine ⟨hcard4, ?_⟩
    have hdvd : Monoid.exponent (P : Subgroup (K ⧸ Z₀)) ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun p => by rw [sq]; exact hsq p
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exfalso
      have hsub := Monoid.exp_eq_one_iff.mp h1
      have h1' : Nat.card (P : Subgroup (K ⧸ Z₀)) ≤ 1 :=
        Finite.card_le_one_iff_subsingleton.mpr hsub
      omega
    · exact h2
  have hnt : Nontrivial (P : Subgroup (K ⧸ Z₀)) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨xb, hxb⟩ := exists_ne (1 : (P : Subgroup (K ⧸ Z₀)))
  obtain ⟨yb, hyb1, hyb⟩ : ∃ yb : (P : Subgroup (K ⧸ Z₀)), yb ≠ 1 ∧ yb ≠ xb := by
    by_contra hc
    push Not at hc
    have hinj : Function.Injective fun z : (P : Subgroup (K ⧸ Z₀)) => decide (z = xb) := by
      intro u v huv
      by_cases hu : u = xb
      · have hv : v = xb := by simpa [hu] using huv.symm
        rw [hu, hv]
      · have hv : v ≠ xb := by simpa [hu] using huv.symm
        have hu1 : u = 1 := by
          by_contra hu1
          exact hu (hc u hu1)
        have hv1 : v = 1 := by
          by_contra hv1
          exact hv (hc v hv1)
        rw [hu1, hv1]
    have := Nat.card_le_card_of_injective _ hinj
    rw [hcard4, Nat.card_eq_fintype_card, Fintype.card_bool] at this
    omega
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z₀ (xb : K ⧸ Z₀)
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Z₀ (yb : K ⧸ Z₀)
  have hxS : x ∈ (S : Subgroup K) := (hmemS x).mpr (hx ▸ xb.2)
  have hyS : y ∈ (S : Subgroup K) := (hmemS y).mpr (hy ▸ yb.2)
  have hx2 : x * x ∈ Z₀ := by
    apply hker
    rw [map_mul, hx]
    exact congrArg Subtype.val (hsq xb)
  have hgen : (S : Subgroup K) ≤ Subgroup.closure {x, y} ⊔ Z₀ := by
    intro s hs
    have hlift : ∀ u : K, u ∈ Subgroup.closure {x, y} → π s = π u →
        s ∈ Subgroup.closure {x, y} ⊔ Z₀ := by
      intro u hu hsu
      have hz : u⁻¹ * s ∈ Z₀ := hker _ (by rw [map_mul, map_inv, hsu, inv_mul_cancel])
      rw [show s = u * (u⁻¹ * s) by group]
      exact Subgroup.mul_mem_sup hu hz
    have hxc : x ∈ Subgroup.closure {x, y} := Subgroup.subset_closure (Set.mem_insert _ _)
    have hyc : y ∈ Subgroup.closure {x, y} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    set sb : (P : Subgroup (K ⧸ Z₀)) := ⟨π s, (hmemS s).mp hs⟩ with hsb
    by_cases hs1 : sb = 1
    · exact Subgroup.mem_sup_right (hker s (congrArg Subtype.val hs1))
    by_cases hsx : sb = xb
    · exact hlift x hxc (by rw [hx]; exact congrArg Subtype.val hsx)
    by_cases hsy : sb = yb
    · exact hlift y hyc (by rw [hy]; exact congrArg Subtype.val hsy)
    have hsxy := IsKleinFour.eq_mul_of_ne_all hxb hyb1 hyb.symm hs1 hsx hsy
    exact hlift (x * y) (Subgroup.mul_mem _ hxc hyc)
      (by rw [map_mul, hx, hy]; exact congrArg Subtype.val hsxy)
  exact card_le_two_of_generators hKp hZc hZ2 S hxS hyS hx2 hgen hcomm

end Small

section Large

theorem mul_self_eq_one_of_transitive {Q : Type*} [Group Q] {T N : Subgroup Q} [Finite T]
    (hT : 2 ∣ Nat.card T)
    (htr : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ n ∈ N, n * x * n⁻¹ = y) :
    ∀ x ∈ T, x * x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 hT
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1, one_mul]
  have hu1 : (u : Q) ≠ 1 := by
    intro h
    have h1 : u = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hu
    omega
  obtain ⟨n, -, hn⟩ := htr x hx hx1 u u.2 hu1
  have hu2 : (u : Q) * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu, sq] at h
    exact congrArg Subtype.val h
  have h : n * (x * x) * n⁻¹ = 1 := by
    calc n * (x * x) * n⁻¹ = (n * x * n⁻¹) * (n * x * n⁻¹) := by group
      _ = 1 := by rw [hn, hu2]
  have h' := congrArg (fun z => n⁻¹ * z * n) h
  simpa [mul_assoc] using h'

theorem commute_of_psl_two_even {K Q : Type*} [Group K] [Finite K] [Group Q] {π : K →* Q}
    (hπ : Function.Surjective π) (hπker : π.ker ≤ Subgroup.center K) {f : ℕ} (hf : 3 ≤ f)
    (e : Q ≃* PSL(2, GaloisField 2 f)) (S : Sylow 2 K) :
    ∀ a ∈ (S : Subgroup K), ∀ b ∈ (S : Subgroup K), a * b = b * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hlarge : 4 < Nat.card (GaloisField 2 f) := by
    rw [hFcard]
    have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hf
    omega
  set η : K →* SL(2, GaloisField 2 f) :=
    ((Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 f)).toMonoidHom.comp
      e.toMonoidHom).comp π with hηdef
  have hηs : Function.Surjective η :=
    (Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 f)).surjective.comp
      (e.surjective.comp hπ)
  have hηker : η.ker ≤ Subgroup.center K := by
    intro k hk
    apply hπker
    rw [MonoidHom.mem_ker] at hk ⊢
    simpa [hηdef] using hk
  have hzero := ShultStronglyClosedTI.linearCoverCommutator_eq_one hlarge η hηs hηker
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL(2, GaloisField 2 f)) (S.mapSurjective hηs)
    (ShultStronglyClosedTI.linearCoverRootSylow f hFcard)
  obtain ⟨k, hk⟩ := hηs g
  have hconj : ∀ a ∈ (S : Subgroup K), η (k * a * k⁻¹) ∈
      ShultStronglyClosedTI.linearCoverRootSubgroup (GaloisField 2 f) := by
    intro a ha
    rw [← ShultStronglyClosedTI.linearCoverRootSylow_coe f hFcard, ← hg, map_mul, map_mul,
      map_inv, hk]
    change g * η a * g⁻¹ ∈ ((g • S.mapSurjective hηs : Sylow 2 SL(2, GaloisField 2 f)) :
      Set SL(2, GaloisField 2 f))
    rw [Sylow.coe_smul]
    exact ⟨η a, ⟨a, ha, rfl⟩, rfl⟩
  intro a ha b hb
  obtain ⟨m, hm⟩ := hconj a ha
  obtain ⟨m', hm'⟩ := hconj b hb
  have hc := ShultStronglyClosedTI.linearCoverCommutator_eq_of_lifts η hηs hηker
    (x := m.toAdd) (y := m'.toAdd) hm.symm hm'.symm
  rw [hzero] at hc
  have h1 : ⁅k * a * k⁻¹, k * b * k⁻¹⁆ = 1 := hc.symm
  rw [← conjugate_commutatorElement] at h1
  have h2 : ⁅a, b⁆ = 1 := by
    have h' := congrArg (fun z => k⁻¹ * z * k) h1
    simpa [mul_assoc] using h'
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

theorem eq_bot_of_eight_le (hSC : Walter.SimpleCaseHyp) {K : Type} [Group K] [Finite K]
    {Z₀ : Subgroup K} [Z₀.Normal] (hK : CFSG.Open.IsQuasisimple K)
    (hZc : Z₀ ≤ Subgroup.center K) (hZ2 : IsPGroup 2 Z₀) (P : Sylow 2 (K ⧸ Z₀))
    (hP : IsMulCommutative (P : Subgroup (K ⧸ Z₀)))
    (h8 : 8 ≤ Nat.card (P : Subgroup (K ⧸ Z₀))) : Z₀ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKp, hKs⟩ := hK
  obtain ⟨S, hS⟩ := exists_sylow_comap hZ2 P
  have hcomm : ∀ a ∈ (S : Subgroup K), ∀ b ∈ (S : Subgroup K), ⁅a, b⁆ ∈ Z₀ := fun a ha b hb =>
    commutatorElement_mem_of_comap hP (hS ▸ ha) (hS ▸ hb)
  have hSZ : (S : Subgroup K) ⊓ Subgroup.center K ≤ Z₀ := by
    have h := le_commutator_sylow hKp S
      (inf_le_right : (S : Subgroup K) ⊓ Subgroup.center K ≤ Subgroup.center K)
      (S.isPGroup'.to_le inf_le_left)
    refine h.trans ?_
    rw [Subgroup.commutator_le]
    exact hcomm
  suffices hab : ∀ a ∈ (S : Subgroup K), ∀ b ∈ (S : Subgroup K), a * b = b * a from
    eq_bot_of_sylow_commute hKp S hab hZc hZ2
  set Q := K ⧸ Subgroup.center K
  have : IsSimpleGroup Q := hKs
  set π : K →* Q := QuotientGroup.mk' (Subgroup.center K) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker = Subgroup.center K := QuotientGroup.ker_mk' _
  set Pb : Sylow 2 Q := S.mapSurjective hπ with hPbdef
  have hPbmem : ∀ a ∈ (S : Subgroup K), π a ∈ (Pb : Subgroup Q) := fun a ha => by
    rw [hPbdef, Sylow.coe_mapSurjective]
    exact Subgroup.mem_map_of_mem π ha
  have hPbc : ∀ u ∈ (Pb : Subgroup Q), ∀ v ∈ (Pb : Subgroup Q), u * v = v * u := by
    intro u hu v hv
    rw [hPbdef, Sylow.coe_mapSurjective] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, ← MonoidHom.mem_ker,
      hπker]
    exact hZc (hcomm a ha b hb)
  have hcardPb : Nat.card (Pb : Subgroup Q) = Nat.card (P : Subgroup (K ⧸ Z₀)) := by
    set ψ := π.comp (S : Subgroup K).subtype with hψ
    set ψ₀ := (QuotientGroup.mk' Z₀).comp (S : Subgroup K).subtype with hψ₀
    have hker : ψ.ker = ψ₀.ker := by
      ext s
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hψ, hψ₀, MonoidHom.comp_apply,
        MonoidHom.comp_apply, Subgroup.coe_subtype, ← MonoidHom.mem_ker, ← MonoidHom.mem_ker,
        hπker, QuotientGroup.ker_mk']
      exact ⟨fun h => hSZ ⟨s.2, h⟩, fun h => hZc h⟩
    have h1 : ψ.range = (Pb : Subgroup Q) := by
      rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype, hPbdef, Sylow.coe_mapSurjective]
    have h2 : ψ₀.range = (P : Subgroup (K ⧸ Z₀)) := by
      rw [hψ₀, MonoidHom.range_comp, Subgroup.range_subtype, hS,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z₀)]
    rw [← h1, ← h2, ← Subgroup.index_ker, ← Subgroup.index_ker, hker]
  have hnonab : ∃ a b : Q, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hle : commutator K ≤ Subgroup.center K := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [← hπker, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hc _ _
    rw [hKp] at hle
    obtain ⟨u, v, huv⟩ := exists_pair_ne Q
    obtain ⟨a, rfl⟩ := hπ u
    obtain ⟨b, rfl⟩ := hπ v
    apply huv
    have ha : π a = 1 := by rw [← MonoidHom.mem_ker, hπker]; exact hle (Subgroup.mem_top a)
    have hb : π b = 1 := by rw [← MonoidHom.mem_ker, hπker]; exact hle (Subgroup.mem_top b)
    rw [ha, hb]
  have hPbab : IsMulCommutative (Pb : Subgroup Q) :=
    ⟨⟨fun u v => Subtype.ext (hPbc _ u.2 _ v.2)⟩⟩
  have habQ : Walter.HasAbelianSylowTwo Q := Walter.hasAbelianSylowTwo_of_sylow Pb hPbab
  have h2Q : 2 ∣ Nat.card Q := by
    refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card (Pb : Subgroup Q))
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp Pb.isPGroup'
    rw [hk]
    rcases k with _ | k
    · rw [hcardPb] at hk
      omega
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  rcases hSC Q hKs hnonab habQ
      (fun H _ => Walter.isAStar_of_hasAbelianSylowTwo hSC (habQ.subgroup H)) with hL2 | hJR
  · rcases hL2 with ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpodd, hf, -, hmod, ⟨e⟩⟩
    ·
      have hf3 : 3 ≤ f := by
        obtain ⟨U₀⟩ : Nonempty (Sylow 2 PSL(2, GaloisField 2 f)) := inferInstance
        have hU₀ := (Walter.psl2_even_sylow_two hf U₀).2
        have hcardQ : Nat.card Q = Nat.card PSL(2, GaloisField 2 f) := Nat.card_congr e.toEquiv
        have h2f : Nat.card (Pb : Subgroup Q) = 2 ^ f := by
          rw [Sylow.card_eq_multiplicity, hcardQ, ← Sylow.card_eq_multiplicity U₀, hU₀]
        by_contra hlt
        have hf2 : f = 2 := by omega
        rw [hf2] at h2f
        omega
      exact commute_of_psl_two_even hπ (le_of_eq hπker) hf3 e S
    ·
      exfalso
      have := hp
      obtain ⟨U₀⟩ : Nonempty (Sylow 2 PSL(2, GaloisField p f)) := inferInstance
      have hU₀ : Nat.card (U₀ : Subgroup PSL(2, GaloisField p f)) = 4 := by
        have := Walter.psl2_odd_sylow_two_isKleinFour hpodd hf hmod U₀
        exact IsKleinFour.card_four
      have hcardQ : Nat.card Q = Nat.card PSL(2, GaloisField p f) := Nat.card_congr e.toEquiv
      have h4 : Nat.card (Pb : Subgroup Q) = 4 := by
        rw [Sylow.card_eq_multiplicity, hcardQ, ← Sylow.card_eq_multiplicity U₀, hU₀]
      omega
  ·
    obtain ⟨-, hcard8⟩ := hJR.sylow_two h2Q Pb
    obtain ⟨htr, g, hgN, -, hg7, hgtr⟩ :=
      Walter.sylow_two_card_eight_transitive hnonab Pb hPbab hcard8
    have hT2 : ∀ x ∈ (Pb : Subgroup Q), x * x = 1 :=
      mul_self_eq_one_of_transitive (by rw [hcard8]; norm_num) htr
    obtain ⟨h, hh⟩ := hπ g
    intro a ha b hb
    exact commute_of_transitive_seven π (le_of_eq hπker) (Pb : Subgroup Q) hPbc hT2
      (fun x hx => (Subgroup.mem_normalizer_iff.mp hgN x).mp hx)
      (fun x hx => by rw [← Subgroup.mem_centralizer_iff.mp hg7 x hx, mul_inv_cancel_right])
      hgtr hh (hPbmem a ha) (hPbmem b hb)

end Large

theorem walter_schur_two_part_of_simpleCaseHyp (hSC : Walter.SimpleCaseHyp) :
    ∀ (K : Type) [Group K] [Finite K] (Z₀ : Subgroup K) [Z₀.Normal],
      CFSG.Open.IsQuasisimple K → Z₀ ≤ Subgroup.center K → IsPGroup 2 Z₀ →
      ∀ P : Sylow 2 (K ⧸ Z₀), IsMulCommutative (P : Subgroup (K ⧸ Z₀)) →
        Nat.card Z₀ ≤ 2 ∧ (8 ≤ Nat.card P → Z₀ = ⊥) := by
  intro K _ _ Z₀ _ hK hZc hZ2 P hP
  by_cases h8 : 8 ≤ Nat.card (P : Subgroup (K ⧸ Z₀))
  · have hbot := eq_bot_of_eight_le hSC hK hZc hZ2 P hP h8
    refine ⟨?_, fun _ => hbot⟩
    rw [hbot, Subgroup.card_bot]
    norm_num
  · exact ⟨card_le_two_of_card_lt_eight hK.1 hZc hZ2 P hP (by omega), fun h => absurd h h8⟩

end CFSG.ComponentClassification.WalterSchur
