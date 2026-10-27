module

public import CFSG.ClassicalInvolution.Sp62Rec.Pkg

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance CFSG.Open

variable {G : Type} [Group G] [Finite G] {z e : G}
  {E B : Subgroup G} {T : Sylow 2 G} {A X : Subgroup G} {A0 : Subgroup (StatedSp 3 (ZMod 2))}

private theorem card_le_of_isPGroup_two (hT : Nat.card (T : Subgroup G) = 512) {R : Subgroup G}
    (hR : IsPGroup 2 R) : Nat.card R ≤ 512 := by
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  have hS : Nat.card (S : Subgroup G) = Nat.card (T : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity S, Sylow.card_eq_multiplicity T]
  calc Nat.card R ≤ Nat.card (S : Subgroup G) := Subgroup.card_le_of_le hRS
    _ = 512 := by rw [hS, hT]

private theorem map_subgroupOf_eq_of_normal {M H : Type} [Group M] [Group H] {X A : Subgroup H}
    {N A0' : Subgroup M} (ψ : ↥X →* ↥N) (hψinj : Function.Injective ψ)
    (hψsurj : Function.Surjective ψ) (hAX : A ≤ X) (hAXN : (A.subgroupOf X).Normal)
    (hA : Nat.card A = 64) (hA0 : Nat.card A0' = 64)
    (hA0N : ∀ Q : Subgroup M, Q ≤ N → (∀ n ∈ N, ∀ x ∈ Q, n * x * n⁻¹ ∈ Q) → IsPGroup 2 Q →
      Q ≤ A0') :
    (A.subgroupOf X).map ψ = A0'.subgroupOf N := by
  have hB : ((A.subgroupOf X).map ψ).Normal := hAXN.map ψ hψsurj
  have hBcard : Nat.card ((A.subgroupOf X).map ψ) = 64 := by
    rw [Subgroup.card_map_of_injective hψinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv, hA]
  have hQcard : Nat.card (((A.subgroupOf X).map ψ).map N.subtype) = 64 := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, hBcard]
  have hQN : ((A.subgroupOf X).map ψ).map N.subtype ≤ N := Subgroup.map_subtype_le _
  have hQnorm : ∀ n ∈ N, ∀ x ∈ ((A.subgroupOf X).map ψ).map N.subtype,
      n * x * n⁻¹ ∈ ((A.subgroupOf X).map ψ).map N.subtype := by
    intro n hn x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨n, hn⟩ * y * ⟨n, hn⟩⁻¹, hB.conj_mem y hy ⟨n, hn⟩, ?_⟩
    rfl
  haveI : Finite (((A.subgroupOf X).map ψ).map N.subtype) :=
    Nat.finite_of_card_ne_zero (by rw [hQcard]; norm_num)
  have hQ2 : IsPGroup 2 (((A.subgroupOf X).map ψ).map N.subtype) :=
    IsPGroup.iff_card.mpr ⟨6, hQcard.trans (by norm_num)⟩
  have hle := hA0N _ hQN hQnorm hQ2
  haveI : Finite A0' := Nat.finite_of_card_ne_zero (by rw [hA0]; norm_num)
  have hQeq : ((A.subgroupOf X).map ψ).map N.subtype = A0' :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hA0, hQcard]))
  have key := Subgroup.comap_map_eq_self_of_injective N.subtype_injective
    ((A.subgroupOf X).map ψ)
  rw [hQeq] at key
  exact key.symm

theorem E8ZPkg.exists_nu (P : E8ZPkg z e E B T A X)
    (hCA : Subgroup.centralizer (A : Set G) = A) (hT : Nat.card (T : Subgroup G) = 512)
    (hN0 : Nat.card N0 = 10752) (hA0 : Nat.card A0 = 64)
    (hA0N : ∀ Q : Subgroup (StatedSp 3 (ZMod 2)), Q ≤ N0 →
      (∀ n ∈ N0, ∀ x ∈ Q, n * x * n⁻¹ ∈ Q) → IsPGroup 2 Q → Q ≤ A0) :
    A ≤ X ∧ ∃ ν : ↥X ≃* ↥N0, (A.subgroupOf X).map ν.toMonoidHom = A0.subgroupOf N0 := by
  obtain ⟨ψ, hsurj, hker⟩ := P.thm2
  have hKX : oddCoreIn X ≤ X := oddCoreIn_le X
  have hKodd : Odd (Nat.card (oddCoreIn X)) := odd_card_oddCoreIn X
  have hA2 : IsPGroup 2 A := IsPGroup.iff_card.mpr ⟨6, P.e64.2.2.trans (by norm_num)⟩
  have hXcard : Nat.card X = 10752 * Nat.card (oddCoreIn X) := by
    have hkerCard : Nat.card ψ.ker = Nat.card (oddCoreIn X) := by
      rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).toEquiv, hN0,
      hkerCard] at h1
    exact h1
  have h2dvd : 2 ^ 9 ∣ Nat.card X := by
    rw [hXcard]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨K₂, hK₂⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥X) 2 h2dvd
  obtain ⟨Q, hQX, hQ2, hQcard⟩ : ∃ Q : Subgroup G, Q ≤ X ∧ IsPGroup 2 Q ∧ Nat.card Q = 512 :=
    ⟨K₂.map X.subtype, Subgroup.map_subtype_le _,
      (IsPGroup.iff_card.mpr ⟨9, hK₂⟩ : IsPGroup 2 K₂).map X.subtype,
      (by rw [Subgroup.card_map_of_injective X.subtype_injective, hK₂] <;> norm_num)⟩
  have hQA : Q = Q ⊔ A := by
    have hsup : IsPGroup 2 (Q ⊔ A : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hQ2 hA2 (hQX.trans P.X_le)
    have hle : Nat.card (Q ⊔ A : Subgroup G) ≤ Nat.card Q := by
      rw [hQcard]
      exact card_le_of_isPGroup_two hT hsup
    exact Subgroup.eq_of_le_of_card_ge le_sup_left hle
  have hAQ : A ≤ Q := by
    rw [hQA]
    exact le_sup_right
  have hAX : A ≤ X := hAQ.trans hQX
  have hcop : Nat.Coprime (Nat.card (oddCoreIn X)) (Nat.card A) := by
    rw [P.e64.2.2]
    exact Nat.Coprime.pow_right 6 (Nat.coprime_two_right.mpr hKodd)
  have hKA : oddCoreIn X ⊓ A = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  have hKcent : oddCoreIn X ≤ Subgroup.centralizer (A : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hc1 : k * a * k⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (P.X_le (hKX hk)) a).mp ha
    have hc2 : a * k⁻¹ * a⁻¹ ∈ oddCoreIn X :=
      conj_mem_oddCoreIn (hAX ha) ((oddCoreIn X).inv_mem hk)
    have hc : k * a * k⁻¹ * a⁻¹ ∈ oddCoreIn X ⊓ A := by
      refine ⟨?_, A.mul_mem hc1 (A.inv_mem ha)⟩
      have e : k * a * k⁻¹ * a⁻¹ = k * (a * k⁻¹ * a⁻¹) := by simp only [mul_assoc]
      rw [e]
      exact (oddCoreIn X).mul_mem hk hc2
    rw [hKA, Subgroup.mem_bot] at hc
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc)).symm
  have hKbot : oddCoreIn X = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    have hkA : k ∈ A := by
      have h := hKcent hk
      rw [hCA] at h
      exact h
    have hk' : k ∈ oddCoreIn X ⊓ A := ⟨hk, hkA⟩
    rw [hKA] at hk'
    exact hk'
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxK : (x : G) ∈ oddCoreIn X := by
      have hxker : x ∈ ψ.ker := MonoidHom.mem_ker.mpr hx
      rw [hker, Subgroup.mem_subgroupOf] at hxker
      exact hxker
    rw [hKbot, Subgroup.mem_bot] at hxK
    exact Subtype.ext hxK
  refine ⟨hAX, MulEquiv.ofBijective ψ ⟨hψinj, hsurj⟩, ?_⟩
  have hAXN : (A.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff hAX).mpr fun h k hh hk =>
      (Subgroup.mem_normalizer_iff.mp (P.X_le hk) h).mp hh
  exact map_subgroupOf_eq_of_normal ψ hψinj hsurj hAX hAXN P.e64.2.2 hA0 hA0N

theorem E8ZPkg.centralizer_A_eq_of_le (P : E8ZPkg z e E B T A X)
    (θ : ↥(Subgroup.centralizer ({e} : Set G)) ≃* ↥Hhat)
    (hθe : θ ⟨e, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ = ⟨alpha, alpha_mem_Hhat⟩)
    (hθA : (A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map θ.toMonoidHom =
      A0.subgroupOf Hhat)
    (hαA0 : alpha ∈ A0) (hA0H : A0 ≤ Hhat)
    (hCA0 : ∀ x ∈ Hhat, (∀ a ∈ A0, x * a = a * x) → x ∈ A0) :
    e ∈ A ∧ Subgroup.centralizer (A : Set G) = A := by
  have hθA' : ∀ y : ↥(Subgroup.centralizer ({e} : Set G)),
      (y : G) ∈ A ↔ θ y ∈ A0.subgroupOf Hhat := by
    intro y
    rw [← hθA]
    constructor
    · intro hy
      exact Subgroup.mem_map_of_mem θ.toMonoidHom (Subgroup.mem_subgroupOf.mpr hy)
    · intro hy
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hy
      have hwy' : θ w = θ y := hwy
      rw [← θ.injective hwy']
      exact Subgroup.mem_subgroupOf.mp hw
  have he : e ∈ A :=
    (hθA' ⟨e, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩).mpr (by
      rw [hθe]
      exact Subgroup.mem_subgroupOf.mpr hαA0)
  refine ⟨he, le_antisymm ?_ ?_⟩
  · intro c hc
    have hcC : c ∈ Subgroup.centralizer ({e} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hc e he).symm
    have hθc : (θ ⟨c, hcC⟩ : StatedSp 3 (ZMod 2)) ∈ A0 := by
      apply hCA0 _ (θ ⟨c, hcC⟩).2
      intro a ha
      obtain ⟨y, hyθ⟩ : ∃ y : ↥(Subgroup.centralizer ({e} : Set G)),
          θ y = ⟨a, hA0H ha⟩ := ⟨θ.symm ⟨a, hA0H ha⟩, θ.apply_symm_apply _⟩
      have hyA : (y : G) ∈ A := (hθA' y).mpr (by
        rw [hyθ]
        exact Subgroup.mem_subgroupOf.mpr ha)
      have hyc : (y : G) * c = c * (y : G) := Subgroup.mem_centralizer_iff.mp hc _ hyA
      have hcomm : (⟨c, hcC⟩ : ↥(Subgroup.centralizer ({e} : Set G))) * y = y * ⟨c, hcC⟩ :=
        Subtype.ext hyc.symm
      have h2 : θ ⟨c, hcC⟩ * θ y = θ y * θ ⟨c, hcC⟩ := by
        rw [← map_mul, ← map_mul, hcomm]
      rw [hyθ] at h2
      exact congrArg Subtype.val h2
    have hθcH : θ ⟨c, hcC⟩ ∈ A0.subgroupOf Hhat := Subgroup.mem_subgroupOf.mpr hθc
    exact (hθA' ⟨c, hcC⟩).mpr hθcH
  · intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => P.e64.1 h hh a ha

end CFSG.ClassicalInvolution.Sp62Rec
