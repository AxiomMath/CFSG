module

public import CFSG.ClassicalInvolution.Sp62Rec.NACountZ6Defs
import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1CE
import CFSG.ClassicalInvolution.Sp62Rec.NACountZ6Model
import CFSG.ClassicalInvolution.Sp62Rec.NACountZ6Weak

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open

namespace Z6NA

private theorem exists_mem_normalizer_sdiff {G : Type*} [Group G] [Finite G] {T Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hTQ : T ≤ Q) (hne : T ≠ Q) :
    ∃ p ∈ Q, p ∈ Subgroup.normalizer (T : Set G) ∧ p ∉ T := by
  haveI : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hlt : T.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne ?_
    refine le_antisymm hTQ fun x hx => ?_
    have : (⟨x, hx⟩ : ↥Q) ∈ T.subgroupOf Q := by rw [h]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have hnc := (Group.normalizerCondition_of_isNilpotent (G := ↥Q)) _ hlt
  obtain ⟨s, hsN, hsT⟩ := SetLike.exists_of_lt hnc
  refine ⟨s, s.2, ?_, fun h => hsT (Subgroup.mem_subgroupOf.mpr h)⟩
  have h1 : s ∈ (Subgroup.normalizer (T : Set G)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hTQ]
    exact hsN
  exact Subgroup.mem_subgroupOf.mp h1

section Model


private theorem aut_mem_A0 (φ : ↥S0 ≃* ↥S0) (x : ↥S0) (hx : (x : StatedSp 3 (ZMod 2)) ∈ A0) :
    ((φ x : ↥S0) : StatedSp 3 (ZMod 2)) ∈ A0 := by
  set f : ↥S0 →* StatedSp 3 (ZMod 2) := S0.subtype.comp φ.toMonoidHom
  have hfinj : Function.Injective f := S0.subtype_injective.comp φ.injective
  set B : Subgroup (StatedSp 3 (ZMod 2)) := (A0.subgroupOf S0).map f
  have hBS : B ≤ S0 := by
    rintro _ ⟨y, -, rfl⟩
    exact (φ y).2
  have hBE : IsE64 B := by
    obtain ⟨hc, hs, hcard⟩ := isE64_A0
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc _ (Subgroup.mem_subgroupOf.mp ha') _ (Subgroup.mem_subgroupOf.mp hb'))
    · intro a ha
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      rw [← map_mul]
      have : a' * a' = 1 := Subtype.ext (hs _ (Subgroup.mem_subgroupOf.mp ha'))
      rw [this, map_one]
    · rw [Subgroup.card_map_of_injective hfinj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe A0_le_S0).toEquiv, hcard]
  have hBeq : B = A0 := eq_A0_of_isE64 B hBS hBE
  have : ((φ x : ↥S0) : StatedSp 3 (ZMod 2)) ∈ B :=
    ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rwa [hBeq] at this

private theorem mem_normalizer_of_mem_normalizer {G : Type*} [Group G] {T A : Subgroup G}
    (θ : ↥T ≃* ↥S0) (hAT : A ≤ T)
    (hAθ : ∀ a (ha : a ∈ T), a ∈ A ↔ ((θ ⟨a, ha⟩ : ↥S0) : StatedSp 3 (ZMod 2)) ∈ A0) {p : G}
    (hp : p ∈ Subgroup.normalizer (T : Set G)) : p ∈ Subgroup.normalizer (A : Set G) := by
  have key : ∀ q ∈ Subgroup.normalizer (T : Set G), ∀ a ∈ A, q * a * q⁻¹ ∈ A := by
    intro q hq a ha
    have haT : a ∈ T := hAT ha
    have hqT : q * a * q⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hq a).mp haT
    set φ : ↥S0 ≃* ↥S0 :=
      θ.symm.trans (((Subgroup.normalizerMonoidHom (T : Subgroup G)) ⟨q, hq⟩).trans θ) with hφ
    have h1 : φ (θ ⟨a, haT⟩) = θ ⟨q * a * q⁻¹, hqT⟩ := by
      simp only [hφ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      exact congrArg θ (Subtype.ext rfl)
    have h2 := aut_mem_A0 φ (θ ⟨a, haT⟩) ((hAθ a haT).mp ha)
    rw [h1] at h2
    exact (hAθ _ hqT).mpr h2
  refine Subgroup.mem_normalizer_iff.mpr fun a => ⟨fun ha => key p hp a ha, fun ha => ?_⟩
  have := key p⁻¹ ((Subgroup.normalizer (T : Set G)).inv_mem hp) _ ha
  simpa [mul_assoc] using this

private theorem isE64_of_theta {G : Type} [Group G] {T A : Subgroup G} (θ : ↥T ≃* ↥S0)
    (hAT : A ≤ T)
    (hAθ : ∀ a (ha : a ∈ T), a ∈ A ↔ ((θ ⟨a, ha⟩ : ↥S0) : StatedSp 3 (ZMod 2)) ∈ A0) :
    IsE64 A := by
  obtain ⟨hc, hs, hcard⟩ := isE64_A0
  have hθA : (A.subgroupOf T).map θ.toMonoidHom = A0.subgroupOf S0 := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      hAθ (θ.symm y).1 (θ.symm y).2]
    have h2 : θ ⟨(θ.symm y).1, (θ.symm y).2⟩ = y := θ.apply_symm_apply y
    rw [h2]
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_, ?_⟩
  · have h1 : θ ⟨a, hAT ha⟩ * θ ⟨b, hAT hb⟩ = θ ⟨b, hAT hb⟩ * θ ⟨a, hAT ha⟩ :=
      Subtype.ext (hc _ ((hAθ a (hAT ha)).mp ha) _ ((hAθ b (hAT hb)).mp hb))
    rw [← map_mul, ← map_mul] at h1
    exact congrArg (fun z : ↥T => (z : G)) (θ.injective h1)
  · have h1 : θ ⟨a, hAT ha⟩ * θ ⟨a, hAT ha⟩ = 1 :=
      Subtype.ext (hs _ ((hAθ a (hAT ha)).mp ha))
    rw [← map_mul, ← map_one θ] at h1
    exact congrArg (fun z : ↥T => (z : G)) (θ.injective h1)
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAT).toEquiv,
      ← Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective, hθA,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe A0_le_S0).toEquiv, card_A0]

end Model

section Restrict


private theorem exists_mulEquiv_restrict {G : Type*} [Group G] {X H : Subgroup G} (hHX : H ≤ X)
    (ν : ↥X →* ↥N0) {K : Subgroup (StatedSp 3 (ZMod 2))} (hKN : K ≤ N0)
    (hK : (H.subgroupOf X).map ν = K.subgroupOf N0)
    (hinj : Function.Injective (ν.comp (Subgroup.inclusion hHX))) :
    ∃ r : ↥H ≃* ↥K, ∀ h : ↥H,
      ((r h : ↥K) : StatedSp 3 (ZMod 2)) = ((ν ⟨h.1, hHX h.2⟩ : ↥N0) : StatedSp 3 (ZMod 2)) := by
  have hmem : ∀ h : ↥H, ((ν ⟨h.1, hHX h.2⟩ : ↥N0) : StatedSp 3 (ZMod 2)) ∈ K := by
    intro h
    have h1 : ν ⟨h.1, hHX h.2⟩ ∈ (H.subgroupOf X).map ν :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr h.2)
    rw [hK] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  let r0 : ↥H →* ↥K := MonoidHom.mk'
    (fun h => ⟨((ν ⟨h.1, hHX h.2⟩ : ↥N0) : StatedSp 3 (ZMod 2)), hmem h⟩) (by
      intro a b
      have h := congrArg Subtype.val ((ν.comp (Subgroup.inclusion hHX)).map_mul a b)
      exact Subtype.ext h)
  have hbij : Function.Bijective r0 := by
    refine ⟨fun a b hab => hinj ?_, fun y => ?_⟩
    · have h := congrArg Subtype.val hab
      exact Subtype.ext h
    have h1 : (⟨(y : StatedSp 3 (ZMod 2)), hKN y.2⟩ : ↥N0) ∈ K.subgroupOf N0 :=
      Subgroup.mem_subgroupOf.mpr y.2
    rw [← hK] at h1
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp h1
    have hxH : (x : G) ∈ H := Subgroup.mem_subgroupOf.mp hx
    refine ⟨⟨x.1, hxH⟩, Subtype.ext ?_⟩
    have : (⟨x.1, hHX hxH⟩ : ↥X) = x := Subtype.ext rfl
    show ((ν ⟨x.1, hHX hxH⟩ : ↥N0) : StatedSp 3 (ZMod 2)) = y
    rw [this, hxy]
  exact ⟨MulEquiv.ofBijective r0 hbij, fun h => rfl⟩

end Restrict

section Rho


private theorem exists_rho {G : Type*} [Group G] {A X : Subgroup G} (hAX : A ≤ X)
    (hXN : X ≤ Subgroup.normalizer (A : Set G)) (hCA : Subgroup.centralizer (A : Set G) = A)
    (ν : ↥X →* ↥N0) (hνA : (A.subgroupOf X).map ν = A0.subgroupOf N0)
    (hdisj : Disjoint (A.subgroupOf X) ν.ker) :
    ∃ ρ : ↥(Subgroup.normalizer (A : Set G)) →* MulAut ↥A0,
      ρ.ker = A.subgroupOf (Subgroup.normalizer (A : Set G)) ∧
      ∀ (x : G) (hx : x ∈ X), ρ ⟨x, hXN hx⟩ = conjA0 (ν ⟨x, hx⟩) := by
  have hinjA : Function.Injective (ν.comp (Subgroup.inclusion hAX)) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (⟨a.1, hAX a.2⟩ : ↥X) ∈ A.subgroupOf X ⊓ ν.ker :=
      ⟨Subgroup.mem_subgroupOf.mpr a.2, ha⟩
    rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext h2
  obtain ⟨νA, hνA_apply⟩ := exists_mulEquiv_restrict hAX ν A0_le_N0 hνA hinjA
  refine ⟨(MulAut.congr νA).toMonoidHom.comp (Subgroup.normalizerMonoidHom A), ?_, ?_⟩
  · have hker : ((MulAut.congr νA).toMonoidHom.comp (Subgroup.normalizerMonoidHom A)).ker =
        (Subgroup.normalizerMonoidHom A).ker := by
      ext n
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe]
      exact map_eq_one_iff _ (MulAut.congr νA).injective
    rw [hker, Subgroup.normalizerMonoidHom_ker, hCA]
  · intro x hx
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    have hform : ∀ (m : ↥(Subgroup.normalizer (A : Set G))) (b : ↥A),
        ((A.normalizerMonoidHom m b : ↥A) : G) = (m : G) * (b : G) * (m : G)⁻¹ := fun m b => rfl
    have hab : νA (νA.symm a) = a := νA.apply_symm_apply a
    set b : ↥A := νA.symm a
    show ((νA (A.normalizerMonoidHom ⟨x, hXN hx⟩ b) : ↥A0) : StatedSp 3 (ZMod 2)) = _
    rw [hνA_apply]
    have h2 : (⟨((A.normalizerMonoidHom ⟨x, hXN hx⟩ b : ↥A) : G),
        hAX (A.normalizerMonoidHom ⟨x, hXN hx⟩ b).2⟩ : ↥X) =
        ⟨x, hx⟩ * ⟨b.1, hAX b.2⟩ * ⟨x, hx⟩⁻¹ := Subtype.ext (hform _ _)
    rw [h2, map_mul, map_mul, map_inv, coe_conjA0_apply, ← hab, hνA_apply]
    rfl

end Rho

section Count

private theorem card_inf_ge {G : Type} [Group G] [Finite G] {A X : Subgroup G}
    (hAcard : Nat.card A = 64) (hXN : X ≤ Subgroup.normalizer (A : Set G))
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (h9 : 2 ^ 9 ∣ Nat.card X)
    (hN2 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.normalizer (A : Set G) →
      Nat.card ↥Q ≤ 1024) :
    32 ≤ Nat.card ↥(A ⊓ X) := by
  set Y : Subgroup G := A ⊔ X with hY
  have hXY : X ≤ Y := le_sup_right
  have hYN : Y ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hXN
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hAX
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAX
  have hi : Nat.card (A ⧸ X.subgroupOf A) = Nat.card (↥Y ⧸ X.subgroupOf Y) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A X hAX).toEquiv
  have hXA : Nat.card (X.subgroupOf A) = Nat.card ↥(A ⊓ X) := by
    rw [← Subgroup.inf_subgroupOf_left,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ X ≤ A)).toEquiv]
  have hA : Nat.card A = Nat.card (A ⧸ X.subgroupOf A) * Nat.card ↥(A ⊓ X) := by
    rw [← hXA]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (X.subgroupOf A)
  have hYcard : Nat.card Y = Nat.card (A ⧸ X.subgroupOf A) * Nat.card X := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (X.subgroupOf Y)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv, ← hi] at h1
    exact h1
  set i := Nat.card (A ⧸ X.subgroupOf A) with hi'
  have hidvd : i ∣ 2 ^ 6 := by
    have : i ∣ Nat.card A := ⟨_, hA⟩
    rw [hAcard] at this
    norm_num
    exact this
  obtain ⟨j, hj, hij⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hidvd
  have hj1 : j ≤ 1 := by
    by_contra hj2
    push Not at hj2
    have hdvd : 2 ^ (9 + j) ∣ Nat.card Y := by
      rw [hYcard, hij, pow_add, mul_comm (2 ^ 9)]
      exact mul_dvd_mul_left _ h9
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Y) 2 hdvd
    have hP2 : IsPGroup 2 (P.map Y.subtype) :=
      (IsPGroup.of_card hP : IsPGroup 2 P).map Y.subtype
    have hPle : P.map Y.subtype ≤ Subgroup.normalizer (A : Set G) :=
      (Subgroup.map_subtype_le P).trans hYN
    have hPcard : Nat.card (P.map Y.subtype) = 2 ^ (9 + j) := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Y), hP]
    have h1 := hN2 _ hP2 hPle
    rw [hPcard] at h1
    have : 2 ^ (9 + j) ≥ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hAcard] at hA
  interval_cases j
  · rw [show i = 1 by simpa using hij] at hA
    omega
  · rw [show i = 2 by simpa using hij] at hA
    omega

end Count

end Z6NA

section Main

open Z6NA


theorem naBridge {G : Type} [Group G] [Finite G] (T A X : Subgroup G) {e : G}
    (θ : ↥T ≃* ↥S0) (hAT : A ≤ T)
    (hAθ : ∀ a (ha : a ∈ T), a ∈ A ↔ ((θ ⟨a, ha⟩ : ↥S0) : StatedSp 3 (ZMod 2)) ∈ A0)
    (hCA : Subgroup.centralizer (A : Set G) = A)
    (hN2 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.normalizer (A : Set G) →
      Nat.card ↥Q ≤ 1024)
    (hXN : X ≤ Subgroup.normalizer (A : Set G))
    (hXn : ∀ g ∈ Subgroup.normalizer (A : Set G), X.map (MulAut.conj g).toMonoidHom = X)
    (ν : ↥X →* ↥N0) (hsurj : Function.Surjective ν) (hker : Nat.card ν.ker ≤ 2)
    (hcen : ν.ker ≤ Subgroup.center ↥X) :
    A ≤ X ∧ Subgroup.normalizer (A : Set G) = X ∧ Function.Injective ν ∧
      ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer ({e} : Set G) → T ≤ Q → Q = T := by
  have hAE : IsE64 A := isE64_of_theta θ hAT hAθ
  have hAcard : Nat.card A = 64 := hAE.2.2
  have hT512 : Nat.card T = 512 := by rw [Nat.card_congr θ.toEquiv, card_S0]
  have hXnorm : ∀ n ∈ Subgroup.normalizer (A : Set G), ∀ x ∈ X, n * x * n⁻¹ ∈ X := by
    intro n hn x hx
    have h1 : n * x * n⁻¹ ∈ X.map (MulAut.conj n).toMonoidHom :=
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [hXn n hn] at h1
  have hAnX : A ≤ Subgroup.normalizer (X : Set G) := by
    intro a ha
    have haN : a ∈ Subgroup.normalizer (A : Set G) := Subgroup.le_normalizer ha
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hXnorm a haN x hx, fun hx => ?_⟩
    have := hXnorm a⁻¹ ((Subgroup.normalizer (A : Set G)).inv_mem haN) _ hx
    simpa [mul_assoc] using this
  have h9 : 2 ^ 9 ∣ Nat.card X := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ν.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ν hsurj).toEquiv, card_N0]
      at h1
    rw [h1]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hinf := card_inf_ge hAcard hXN hAnX h9 hN2
  obtain ⟨hAX, hνA, hdisj⟩ := nu_sub hAE hXN ν hsurj hker hinf
  have hνinj : Function.Injective ν := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxz : x ∈ Subgroup.center ↥X := hcen hx
    have hxA : (x : G) ∈ A := by
      rw [← hCA, Subgroup.mem_centralizer_iff]
      intro a ha
      have := Subgroup.mem_center_iff.mp hxz ⟨a, hAX ha⟩
      exact congrArg Subtype.val this
    have hx' : x ∈ A.subgroupOf X ⊓ ν.ker := ⟨Subgroup.mem_subgroupOf.mpr hxA, hx⟩
    rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at hx'
    exact hx'
  obtain ⟨ρ, hρker, hρν⟩ := exists_rho hAX hXN hCA ν hνA hdisj
  have hkey : ∀ n : ↥(Subgroup.normalizer (A : Set G)), ∀ l ∈ Lbar, ρ n * l * (ρ n)⁻¹ ∈ Lbar := by
    intro n l hl
    obtain ⟨m, rfl⟩ := hl
    obtain ⟨x, rfl⟩ := hsurj m
    have hx' : (n : G) * x * (n : G)⁻¹ ∈ X := hXnorm n n.2 x x.2
    have hcalc : ρ n * conjA0 (ν x) * (ρ n)⁻¹ = conjA0 (ν ⟨(n : G) * x * (n : G)⁻¹, hx'⟩) := by
      rw [← hρν x.1 x.2, ← map_inv, ← map_mul, ← map_mul,
        show n * ⟨x.1, hXN x.2⟩ * n⁻¹ = ⟨(n : G) * x * (n : G)⁻¹, hXN hx'⟩ from Subtype.ext rfl,
        hρν _ hx']
    rw [hcalc]
    exact ⟨_, rfl⟩
  have hnormL : ∀ n : ↥(Subgroup.normalizer (A : Set G)),
      ρ n ∈ Subgroup.normalizer (Lbar : Set (MulAut ↥A0)) := by
    intro n
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hkey n h hh, fun hh => ?_⟩
    have h1 := hkey n⁻¹ _ hh
    have h2 : ρ n⁻¹ * (ρ n * h * (ρ n)⁻¹) * (ρ n⁻¹)⁻¹ = h := by
      rw [map_inv, inv_inv]
      group
    rwa [h2] at h1
  have hNX : Subgroup.normalizer (A : Set G) = X := by
    refine le_antisymm (fun n hn => ?_) hXN
    obtain ⟨m, hm⟩ := normalizer_Lbar_le _ (hnormL ⟨n, hn⟩)
    obtain ⟨x, rfl⟩ := hsurj m
    have h1 : ρ (⟨n, hn⟩ * (⟨x.1, hXN x.2⟩ : ↥(Subgroup.normalizer (A : Set G)))⁻¹) = 1 := by
      rw [map_mul, map_inv, hρν x.1 x.2, hm, mul_inv_cancel]
    rw [← MonoidHom.mem_ker, hρker, Subgroup.mem_subgroupOf] at h1
    have h2 : n * (x : G)⁻¹ ∈ X := hAX h1
    have h3 := X.mul_mem h2 x.2
    simpa using h3
  refine ⟨hAX, hNX, hνinj, ?_⟩
  intro Q hQ _ hTQ
  by_contra hne
  obtain ⟨p, hpQ, hpT, hpnT⟩ := exists_mem_normalizer_sdiff hQ hTQ (Ne.symm hne)
  have hTN : ∀ p ∈ Subgroup.normalizer (T : Set G), p ∈ X := fun p hp =>
    hNX ▸ mem_normalizer_of_mem_normalizer θ hAT hAθ hp
  have hTX : T ≤ X := fun t ht => hTN t (Subgroup.le_normalizer ht)
  have hpX : p ∈ X := hTN p hpT
  set R : Subgroup G := T ⊔ Subgroup.zpowers p with hR
  have hRQ : R ≤ Q := sup_le hTQ (Subgroup.zpowers_le.mpr hpQ)
  have hRp : IsPGroup 2 R := hQ.to_le hRQ
  have hRX : R ≤ X := sup_le hTX (Subgroup.zpowers_le.mpr hpX)
  have hXcard : Nat.card X = 10752 := by
    rw [Nat.card_congr (MulEquiv.ofBijective ν ⟨hνinj, hsurj⟩).toEquiv, card_N0]
  have hRcard : Nat.card R ≤ 512 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
    have hdvd : 2 ^ k ∣ 2 ^ 9 * 21 := by
      have := Subgroup.card_dvd_of_le hRX
      rw [hk, hXcard] at this
      norm_num
      exact this
    have hcop : Nat.Coprime (2 ^ k) 21 := Nat.Coprime.pow_left k (by norm_num)
    have h2 : 2 ^ k ∣ 2 ^ 9 := hcop.dvd_of_dvd_mul_right hdvd
    rw [hk]
    exact (Nat.le_of_dvd (by norm_num) h2).trans (by norm_num)
  have hTR : T = R :=
    Subgroup.eq_of_le_of_card_ge (le_sup_left : T ≤ R) (by rw [hT512]; exact hRcard)
  have hpR : p ∈ R := Subgroup.mem_sup_right (Subgroup.mem_zpowers p)
  rw [← hTR] at hpR
  exact hpnT hpR

end Main

end CFSG.ClassicalInvolution.Sp62Rec
