module

public import CFSG.ClassicalInvolution.Q3.TL3T29
public import CFSG.ClassicalInvolution.Q3.TL4D1AE3
public import CFSG.ClassicalInvolution.Q3.TL3T28
public import CFSG.ClassicalInvolution.Q3.TL4D1Comp
public import CFSG.ClassicalInvolution.Q3.TL4D1Out
public import CFSG.ClassicalInvolution.Q3.TL4D1PackB

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

section Core

variable {n : ℕ}

@[expose] def ModelTwCore (𝒜 : Set (Finset (Fin n))) (M : Subgroup (AE.AEQ n)) : Prop :=
  ∀ (B : Subgroup (AE.AEQ n)) (w : AE.AEQ n), B ≤ M → IsUniqueInvolution B w →
    Nat.card ↥B = 8 → (∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x) →
    (∃ T : Subgroup (AE.AEQ n), T ≤ M ∧ (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) ∧
      IsPGroup 2 ↥T ∧ w ∈ T) →
    (∀ T : Subgroup (AE.AEQ n), T ≤ M → (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) →
      IsPGroup 2 ↥T → ∀ x ∈ B, x ∈ T → x = 1 ∨ x = w) →
    (∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool),
      (∃ x ∈ B, orderOf x = 4 ∧ ∀ k ∈ AE.memBar α h b, x * k * x⁻¹ ∈ AE.memBar α h b) →
      Commutes (AE.memBar α h b) B) → False

@[expose] def ModelCenter (M : Subgroup (AE.AEQ n)) : Prop :=
  ∀ m ∈ M, (∀ m' ∈ M, m * m' = m' * m) → m = 1

@[expose] def ModelInvO2 (𝒜 : Set (Finset (Fin n))) (M : Subgroup (AE.AEQ n)) : Prop :=
  ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (T : Subgroup (AE.AEQ n)), T ≤ M →
    (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) → IsPGroup 2 ↥T →
      ∀ t ∈ T, AE.zBar α h * t = t * AE.zBar α h

@[expose] def ModelTwCoreZ (𝒜 : Set (Finset (Fin n))) (M : Subgroup (AE.AEQ n)) : Prop :=
  ∀ (B : Subgroup (AE.AEQ n)) (w : AE.AEQ n), B ≤ M → IsUniqueInvolution B w →
    Nat.card ↥B = 8 → (∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x) →
    (∀ T : Subgroup (AE.AEQ n), T ≤ M → (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) →
      IsPGroup 2 ↥T → ∀ t ∈ T, w * t = t * w) →
    (∀ T : Subgroup (AE.AEQ n), T ≤ M → (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) →
      IsPGroup 2 ↥T → ∀ x ∈ B, x ∈ T → x = 1 ∨ x = w) →
    (∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool),
      (∃ x ∈ B, orderOf x = 4 ∧ ∀ k ∈ AE.memBar α h b, x * k * x⁻¹ ∈ AE.memBar α h b) →
      Commutes (AE.memBar α h b) B) → False

end Core

structure D1TwFacts : Prop where
  e8Normal : TL4.E8NormalFact
  e8Perfect : TL4.E8PerfectFact
  aeNormal : ∀ m : ℕ, 5 ≤ m → TL4.ModelNormal (TL4.aeModel m)
  aePerfect : ∀ m : ℕ, 5 ≤ m → TL4.ModelPerfect (TL4.aeModel m)
  aeCore : ∀ m : ℕ, 5 ≤ m → ModelTwCore (Set.univ : Set (Finset (Fin m))) (TL4.aeModel m)
  e64Normal : TL4.ModelNormal AE.e64Sub
  e64Perfect : TL4.ModelPerfect AE.e64Sub
  e64Three : TL4.ModelThree AE.e64Sets AE.e64Sub
  e64Core : ModelTwCore AE.e64Sets AE.e64Sub
  e29Normal : TL4.ModelNormal AE.e29Sub
  e29Perfect : TL4.ModelPerfect AE.e29Sub
  e29Three : TL4.ModelThree AE.e29Sets AE.e29Sub
  e29Center : ModelCenter AE.e29Sub
  e29Inv : ModelInvO2 AE.e29Sets AE.e29Sub
  e29CoreZ : ModelTwCoreZ AE.e29Sets AE.e29Sub

structure D1TwSub (J X : Subgroup G) : Prop where
  le : J ≤ X
  sub : X.IsSubnormal
  span : pSpan {L | ∃ x ∈ X, conjSub x J = L} = X
  pack : TL4.D1Pack X
  e8 : ∀ E : Subgroup G, E8Struct X E → E ≤ Subgroup.normalizer (J : Set G)
  out : (∃ E : Subgroup G, E8Struct X E) ∨
    (Nat.card J = 8 ∧ ∃ (n : ℕ) (𝒜 : Set (Finset (Fin n))) (M : Subgroup (AE.AEQ n)), 5 ≤ n ∧
      ModelTwCore 𝒜 M ∧ Nonempty (AEIdentOn {L | ∃ x ∈ X, conjSub x J = L} n 𝒜 M)) ∨
    (Nat.card J = 8 ∧ Nonempty (AEIdentOn {L | ∃ x ∈ X, conjSub x J = L} 8 AE.e29Sets AE.e29Sub))

theorem card_eq_eight_of_ident {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ J ∈ Δ, IsPGroup 2 J) {J : Subgroup G} (hJ : J ∈ Δ) {P : Set (Subgroup G)}
    (hPΔ : P ⊆ Δ) (hJP : J ∈ P) (hP : ∀ L ∈ P, ∃ x ∈ pSpan P, conjSub x J = L)
    (hXs : (pSpan P).IsSubnormal) (hJnot : ¬ J ≤ pCore 2 G) {n : ℕ} (hn : 5 ≤ n)
    {𝒜 : Set (Finset (Fin n))} {M : Subgroup (AE.AEQ n)} (I : AEIdentOn P n 𝒜 M) :
    Nat.card J = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJX : J ≤ pSpan P := le_pSpan hJP
  obtain ⟨⟨u, hu⟩, -⟩ := hΩ.omega1 J hJ
  have hu' := isUniqueInvolution_subgroupOf hu hJX
  have hinj : ∀ x ∈ J.subgroupOf (pSpan P), I.φ x = 1 → x = 1 := by
    intro x hx hx1
    by_contra hne
    have hJ2' : IsPGroup 2 ↥(J.subgroupOf (pSpan P)) := (h2 J hJ).comap_subtype
    have hKk2 : IsPGroup 2 ↥(J.subgroupOf (pSpan P) ⊓ I.φ.ker) := hJ2'.to_le inf_le_left
    have hne' : J.subgroupOf (pSpan P) ⊓ I.φ.ker ≠ ⊥ := by
      intro hb
      apply hne
      have : x ∈ J.subgroupOf (pSpan P) ⊓ I.φ.ker := ⟨hx, hx1⟩
      rw [hb] at this
      exact this
    have huk := TL4.mem_of_isPGroup_of_ne_bot hu' inf_le_left hKk2 hne'
    have hucen := I.ker_le huk.2
    have hall : ∀ L ∈ P, IsUniqueInvolution L u := by
      intro L hL
      obtain ⟨x, hx, rfl⟩ := hP L hL
      have h1 := hu.conj x
      have hxu : x * u * x⁻¹ = u := by
        have := Subgroup.mem_center_iff.mp hucen ⟨x, hx⟩
        have h2 : x * u = u * x := congrArg Subtype.val this
        rw [h2]
        group
      rwa [hxu] at h1
    have hXC : (pSpan P) ≤ pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) :=
      pSpan_le fun L hL => le_pCoreOf_centralizer hΩ h2 (hPΔ hL) (hall L hL)
    have hX2 : IsPGroup 2 ↥(pSpan P) := (LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hXC
    exact hJnot (hJX.trans (TL4.le_pCore_of_isSubnormal hXs le_rfl
      (fun w hw x hx => (pSpan P).mul_mem ((pSpan P).mul_mem hw hx) ((pSpan P).inv_mem hw)) hX2))
  obtain ⟨α, -, h, b, hlab⟩ := I.label J hJP
  let f : ↥(J.subgroupOf (pSpan P)) → ↥(AE.memBar α h b) := fun x =>
    ⟨I.φ x, by rw [← hlab]; exact ⟨x, x.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, ?_⟩
    · have h1 : I.φ ((x : ↥(pSpan P)) * (y : ↥(pSpan P))⁻¹) = 1 := by
        rw [map_mul, map_inv]
        have := congrArg Subtype.val hxy
        simp only [f] at this
        rw [this, mul_inv_cancel]
      have h2 := hinj _ ((J.subgroupOf (pSpan P)).mul_mem x.2
        ((J.subgroupOf (pSpan P)).inv_mem y.2)) h1
      exact Subtype.ext (mul_inv_eq_one.mp h2)
    · rintro ⟨z, hz⟩
      obtain ⟨y, hy, rfl⟩ : z ∈ (J.subgroupOf (pSpan P)).map I.φ := by rw [hlab]; exact hz
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [← AE.natCard_memBar hn α h b, ← Nat.card_congr (Equiv.ofBijective f hf),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJX).toEquiv]

theorem exists_d1TwSub (hF : D1TwFacts) {r : ℕ} {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ J ∈ Δ, IsPGroup 2 J) (h8 : ∀ J ∈ Δ, Nat.card J = 2 ^ r) (hA : ∀ J ∈ Δ, AEmpty Δ J)
    (hodd : classicalInvolutionOddCore G = ⊥)
    (hall : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → TightInO2 z)
    (hD2 : ThmDGenBelow r (Nat.card G + 1)) {J : Subgroup G} (hJ : J ∈ Δ)
    (hT : ∀ g : G, ∀ U ∈ USet Δ, U ≤ conjSub g J → ¬ U ≤ pCore 2 G) :
    ∃ X : Subgroup G, D1TwSub J X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hJX, hXs, hspan⟩ := TL4.exists_subnormal_closure J
  set P : Set (Subgroup G) := {L | ∃ x ∈ X, conjSub x J = L} with hP
  have hPΔ : P ⊆ Δ := by
    rintro L ⟨x, -, rfl⟩
    exact hΩ.conjInvariant x J hJ
  have hJP : J ∈ P := ⟨1, X.one_mem, conjSub_one J⟩
  have hPne : P.Nonempty := ⟨J, hJP⟩
  have htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L' := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    refine ⟨x' * x⁻¹, hspan ▸ X.mul_mem hx' (X.inv_mem hx), ?_⟩
    rw [← conjSub_mul, inv_mul_cancel_right]
  have hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P := by
    rintro _ ⟨x', hx', rfl⟩ x hx
    rw [hspan] at hx
    exact ⟨x * x', X.mul_mem hx hx', conjSub_mul x x' J⟩
  have hoddX : classicalInvolutionOddCore ↥(pSpan P) = ⊥ := by
    rw [hspan]
    exact TL4.oddCore_eq_bot_of_isSubnormal hodd hXs
  have hE2 : ∀ L ∈ P, ∀ u' : G, IsUniqueInvolution L u' → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u' ∈ Q := by
    intro L hL u' hu'
    refine ⟨pSpan P ⊓ pCore 2 G, inf_le_left, fun x hx q hq => ⟨?_, ?_⟩,
      pCore_isPGroup.to_le inf_le_right,
      ⟨le_pSpan hL hu'.mem, TL4.mem_pCore_of_tightInO2 (hall L (hPΔ hL) u' hu')⟩⟩
    · exact (pSpan P).mul_mem ((pSpan P).mul_mem hx hq.1) ((pSpan P).inv_mem hx)
    · exact pCore_normal.conj_mem q hq.2 x
  have hcard : Nat.card ↥(pSpan P) < Nat.card G + 1 :=
    Nat.lt_succ_of_le (Subgroup.card_le_card_group _)
  have hout := hD2 G Δ hΩ h2 h8 hA P hPΔ hcard htrans hinv hoddX hE2
  have hXs' : (pSpan P).IsSubnormal := hspan ▸ hXs
  have hPmem : ∀ L ∈ P, ∃ x ∈ pSpan P, conjSub x J = L := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hspan ▸ hx, rfl⟩
  have hJnot : ¬ J ≤ pCore 2 G := by
    intro hJQ
    have hLs : IsSylow2In J J := ⟨le_rfl, h2 J hJ, fun Q hQL _ hLQ => le_antisymm hQL hLQ⟩
    obtain ⟨U, hU, hUJ, -⟩ := Sec6Gen.exists_invariant_mem_USet hΩ hJ hLs (h2 J hJ) le_rfl
      fun q hq => conjSub_eq_self_of_mem hq
    exact hT 1 U hU (by rw [conjSub_one]; exact hUJ) (hUJ.trans hJQ)
  have he8 : ∀ E : Subgroup G, E8Struct X E → E ≤ Subgroup.normalizer (J : Set G) := by
    intro E hE
    rw [← hspan] at hE
    exact le_normalizer_of_e8Struct hΩ h2 h8 hPΔ hinv hE2 hE hJP
  rcases hout with hsing | ⟨W, hW⟩ | ⟨E, hE⟩ | hI64 | ⟨m, hm, hI⟩ | hI29
  · exfalso
    have hXJ : X ≤ J := hspan ▸ pSpan_le fun L hL => (hsing L hL J hJP).le
    have hJs : J.IsSubnormal := (le_antisymm hXJ hJX) ▸ hXs
    exact hJnot (TL4.le_pCore_of_isSubnormal hJs le_rfl
      (fun w hw x hx => J.mul_mem (J.mul_mem hw hx) (J.inv_mem hw)) (h2 J hJ))
  · exfalso
    obtain ⟨hWX, hXN, hW2, J₀, hJ₀, U, hU, hUJ₀, hUW⟩ :=
      exists_of_WIn_eq hΩ h2 hPΔ hPne hinv hW
    have hWQ : W ≤ pCore 2 G := TL4.le_pCore_of_isSubnormal hXs' hWX
      (fun x hx w hw => (Subgroup.mem_normalizer_iff.mp (hXN hx) w).mp hw) hW2
    obtain ⟨g, -, rfl⟩ := hJ₀
    exact hT g U hU hUJ₀ (hUW.trans hWQ)
  · rw [hspan] at hE
    exact ⟨X, hJX, hXs, hspan, TL4.D1Pack.of_e8 hF.e8Normal hF.e8Perfect hE, he8,
      Or.inl ⟨E, hE⟩⟩
  · obtain ⟨I⟩ := hI64
    have hJ8 := card_eq_eight_of_ident hΩ h2 hJ hPΔ hJP hPmem hXs' hJnot (by norm_num) I
    have h8' : ∀ K ∈ Δ, Nat.card K = 8 := fun K hK => by rw [h8 K hK, ← h8 J hJ, hJ8]
    have hpack := TL4.D1Pack.of_ident hΩ h2 h8' hPΔ hinv (by norm_num) I
      (I.toLabel.isPGroup_ker hoddX) hF.e64Normal hF.e64Perfect hF.e64Three hPne
    rw [hspan] at hpack
    exact ⟨X, hJX, hXs, hspan, hpack, he8, Or.inr (Or.inl ⟨hJ8, 7, _, _, by norm_num, hF.e64Core,
      ⟨I⟩⟩)⟩
  · obtain ⟨I⟩ := TL4.nonempty_aeIdentOn_of_aeIdent hI
    have hJ8 := card_eq_eight_of_ident hΩ h2 hJ hPΔ hJP hPmem hXs' hJnot hm I
    have h8' : ∀ K ∈ Δ, Nat.card K = 8 := fun K hK => by rw [h8 K hK, ← h8 J hJ, hJ8]
    have hpack := TL4.D1Pack.of_ident hΩ h2 h8' hPΔ hinv hm I (I.toLabel.isPGroup_ker hoddX)
      (hF.aeNormal m hm) (hF.aePerfect m hm) (TL4.aeModelThree m) hPne
    rw [hspan] at hpack
    exact ⟨X, hJX, hXs, hspan, hpack, he8, Or.inr (Or.inl ⟨hJ8, m, _, _, hm, hF.aeCore m hm,
      ⟨I⟩⟩)⟩
  · obtain ⟨I⟩ := hI29
    have hJ8 := card_eq_eight_of_ident hΩ h2 hJ hPΔ hJP hPmem hXs' hJnot (by norm_num) I
    have h8' : ∀ K ∈ Δ, Nat.card K = 8 := fun K hK => by rw [h8 K hK, ← h8 J hJ, hJ8]
    have hpack := TL4.D1Pack.of_ident hΩ h2 h8' hPΔ hinv (by norm_num) I
      (I.toLabel.isPGroup_ker hoddX) hF.e29Normal hF.e29Perfect hF.e29Three hPne
    rw [hspan] at hpack
    exact ⟨X, hJX, hXs, hspan, hpack, he8, Or.inr (Or.inr ⟨hJ8, ⟨I⟩⟩)⟩

theorem false_of_ident_core_gen {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ J ∈ Δ, IsPGroup 2 J) (h8 : ∀ J ∈ Δ, Nat.card J = 8) (hA : ∀ J ∈ Δ, AEmpty Δ J)
    (hodd : classicalInvolutionOddCore G = ⊥) {J L X : Subgroup G} (hJ : J ∈ Δ) (hL : L ∈ Δ)
    (hnc : ¬ ∃ g : G, conjSub g J = L) {v : G} (hv : IsUniqueInvolution L v)
    (hvQ : v ∈ pCore 2 G) (hvJ : v ∉ Subgroup.normalizer (J : Set G))
    (hthin : ∀ x ∈ L, x ∈ pCore 2 G → x = 1 ∨ x = v)
    (hXs : X.IsSubnormal) (hJX : J ≤ X) (hLX : L ≤ X)
    {P : Set (Subgroup G)} (hPdef : ∀ K, K ∈ P ↔ ∃ x ∈ X, conjSub x J = K)
    (hspan : pSpan P = X) {n : ℕ} (hn : 5 ≤ n)
    {𝒜 : Set (Finset (Fin n))} {M : Subgroup (AE.AEQ n)} (I : AEIdentOn P n 𝒜 M)
    (hc : ∀ (B : Subgroup (AE.AEQ n)) (w : AE.AEQ n), B ≤ M → IsUniqueInvolution B w →
      Nat.card ↥B = 8 → (∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x) →
      (∃ T : Subgroup (AE.AEQ n), T ≤ M ∧ (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) ∧
        IsPGroup 2 ↥T ∧ w ∈ T) →
      (∀ T : Subgroup (AE.AEQ n), T ≤ M → (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) →
        IsPGroup 2 ↥T → ∀ x ∈ B, x ∈ T → x = 1 ∨ x = w) →
      (∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool),
        (∃ x ∈ B, orderOf x = 4 ∧ ∀ k ∈ AE.memBar α h b, x * k * x⁻¹ ∈ AE.memBar α h b) →
        Commutes (AE.memBar α h b) B) →
      (∀ y : ↥(pSpan P), (y : G) = v → I.φ y = w) → False) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pCore 2 G).Normal := pCore_normal
  have hPΔ : P ⊆ Δ := by
    intro K hK
    obtain ⟨x, -, rfl⟩ := (hPdef K).mp hK
    exact hΩ.conjInvariant x J hJ
  have hinv : ∀ K ∈ P, ∀ x ∈ pSpan P, conjSub x K ∈ P := by
    intro K hK x hx
    obtain ⟨x', hx', rfl⟩ := (hPdef K).mp hK
    rw [hspan] at hx
    exact (hPdef _).mpr ⟨x * x', X.mul_mem hx hx', conjSub_mul x x' J⟩
  have hoddX : classicalInvolutionOddCore ↥(pSpan P) = ⊥ := by
    rw [hspan]
    exact TL4.oddCore_eq_bot_of_isSubnormal hodd hXs
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hoddX
  have hXs' : (pSpan P).IsSubnormal := hspan ▸ hXs
  have hLY : L ≤ pSpan P := hspan.symm ▸ hLX
  have hJY : J ≤ pSpan P := hspan.symm ▸ hJX
  have hv' := isUniqueInvolution_subgroupOf hv hLY
  have hL2' : IsPGroup 2 ↥(L.subgroupOf (pSpan P)) := (h2 L hL).comap_subtype
  have hinj : ∀ x ∈ L.subgroupOf (pSpan P), I.φ x = 1 → x = 1 := by
    intro x hx hx1
    by_contra hne
    have hne' : L.subgroupOf (pSpan P) ⊓ I.φ.ker ≠ ⊥ := by
      intro hb
      apply hne
      have : x ∈ L.subgroupOf (pSpan P) ⊓ I.φ.ker := ⟨hx, hx1⟩
      rw [hb] at this
      exact this
    have hvk := TL4.mem_of_isPGroup_of_ne_bot hv' inf_le_left (hL2'.to_le inf_le_left) hne'
    have hvcen := I.ker_le hvk.2
    apply hvJ
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun j hj => ?_)
    have := Subgroup.mem_center_iff.mp hvcen ⟨j, hJY hj⟩
    exact congrArg Subtype.val this
  have hinj' : ∀ x y : ↥(pSpan P), x ∈ L.subgroupOf (pSpan P) → y ∈ L.subgroupOf (pSpan P) →
      I.φ x = I.φ y → x = y := by
    intro x y hx hy hxy
    have h1 : I.φ (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hinj _ ((L.subgroupOf (pSpan P)).mul_mem hx
      ((L.subgroupOf (pSpan P)).inv_mem hy)) h1)
  set v' : ↥(pSpan P) := ⟨v, hLY hv.mem⟩ with hv'def
  set B : Subgroup (AE.AEQ n) := (L.subgroupOf (pSpan P)).map I.φ with hB
  set w : AE.AEQ n := I.φ v' with hw
  have hvL : v' ∈ L.subgroupOf (pSpan P) := Subgroup.mem_subgroupOf.mpr hv.mem
  have hBM : B ≤ M := (Subgroup.map_le_range _ _).trans I.range_eq.le
  have hBw : IsUniqueInvolution B w := by
    refine ⟨⟨v', hvL, rfl⟩, fun h1 => hv.ne_one ?_, ?_, ?_⟩
    · have := hinj v' hvL h1
      exact congrArg Subtype.val this
    · rw [hw, ← map_mul]
      have : v' * v' = 1 := Subtype.ext hv.sq
      rw [this, map_one]
    · rintro _ ⟨y, hy, rfl⟩ hyy
      have h1 : I.φ (y * y) = 1 := by rw [map_mul]; exact hyy
      have h2 := hinj _ ((L.subgroupOf (pSpan P)).mul_mem hy hy) h1
      rcases hv.unique (y : G) (Subgroup.mem_subgroupOf.mp hy) (congrArg Subtype.val h2) with
        h3 | h3
      · left
        rw [show y = 1 from Subtype.ext h3, map_one]
      · right
        rw [show y = v' from Subtype.ext h3]
  have hB8 : Nat.card ↥B = 8 := by
    let f : ↥(L.subgroupOf (pSpan P)) → ↥B := fun x => ⟨I.φ x, ⟨x, x.2, rfl⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨fun x y hxy => Subtype.ext (hinj' _ _ x.2 y.2 (congrArg Subtype.val hxy)), ?_⟩
      rintro ⟨_, ⟨y, hy, rfl⟩⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLY).toEquiv, h8 L hL]
  have hBnc : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΩ
      (TC.mem_RSet_of_isPGroup hL (h2 L hL))).exists_not_commute
    refine ⟨I.φ ⟨x, hLY hx⟩, ⟨_, Subgroup.mem_subgroupOf.mpr hx, rfl⟩,
      I.φ ⟨y, hLY hy⟩, ⟨_, Subgroup.mem_subgroupOf.mpr hy, rfl⟩, fun h => hxy ?_⟩
    rw [← map_mul, ← map_mul] at h
    have := hinj' _ _ ((L.subgroupOf (pSpan P)).mul_mem (Subgroup.mem_subgroupOf.mpr hx)
      (Subgroup.mem_subgroupOf.mpr hy)) ((L.subgroupOf (pSpan P)).mul_mem
      (Subgroup.mem_subgroupOf.mpr hy) (Subgroup.mem_subgroupOf.mpr hx)) h
    exact congrArg Subtype.val this
  have hrange : ∀ m ∈ M, ∃ y : ↥(pSpan P), I.φ y = m := fun m hm => by
    rw [← I.range_eq] at hm
    exact hm
  have hT : ∃ T : Subgroup (AE.AEQ n), T ≤ M ∧ (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) ∧
      IsPGroup 2 ↥T ∧ w ∈ T := by
    refine ⟨((pCore 2 G).subgroupOf (pSpan P)).map I.φ,
      (Subgroup.map_le_range _ _).trans I.range_eq.le, ?_, ?_, ⟨v', ?_, rfl⟩⟩
    · rintro m hm _ ⟨q, hq, rfl⟩
      obtain ⟨y, rfl⟩ := hrange m hm
      refine ⟨y * q * y⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact pCore_normal.conj_mem _ (Subgroup.mem_subgroupOf.mp hq) y
    · have hQ2' : IsPGroup 2 ↥((pCore 2 G).subgroupOf (pSpan P)) := pCore_isPGroup.comap_subtype
      exact hQ2'.map _
    · exact Subgroup.mem_subgroupOf.mpr hvQ
  have hthinB : ∀ T : Subgroup (AE.AEQ n), T ≤ M → (∀ x ∈ M, ∀ t ∈ T, x * t * x⁻¹ ∈ T) →
      IsPGroup 2 ↥T → ∀ x ∈ B, x ∈ T → x = 1 ∨ x = w := by
    rintro T - hTn hT2 _ ⟨y, hy, rfl⟩ hyT
    have hT'2 : IsPGroup 2 ↥(T.comap I.φ) := hT2.comap_of_ker_isPGroup I.φ hk
    have hle : (T.comap I.φ).map (pSpan P).subtype ≤ pCore 2 G := by
      refine TL4.le_pCore_of_isSubnormal hXs' (Subgroup.map_subtype_le _) ?_ (hT'2.map _)
      rintro z hz _ ⟨t, ht, rfl⟩
      refine ⟨⟨z, hz⟩ * t * ⟨z, hz⟩⁻¹, ?_, rfl⟩
      show I.φ (⟨z, hz⟩ * t * ⟨z, hz⟩⁻¹) ∈ T
      rw [map_mul, map_mul, map_inv]
      exact hTn _ (I.range_eq.le ⟨_, rfl⟩) _ ht
    have hyQ : (y : G) ∈ pCore 2 G := hle ⟨y, hyT, rfl⟩
    rcases hthin (y : G) (Subgroup.mem_subgroupOf.mp hy) hyQ with h1 | h1
    · left
      rw [show y = 1 from Subtype.ext h1, map_one]
    · right
      rw [show y = v' from Subtype.ext h1]
  have hi : ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool),
      (∃ x ∈ B, orderOf x = 4 ∧ ∀ k ∈ AE.memBar α h b, x * k * x⁻¹ ∈ AE.memBar α h b) →
      Commutes (AE.memBar α h b) B := by
    rintro α hα h b ⟨_, ⟨y, hy, rfl⟩, hxo, hxN⟩
    obtain ⟨J', hJ'P, hlab⟩ := I.label_surj α hα h b
    have hJ'Δ : J' ∈ Δ := hPΔ hJ'P
    have hJ'Y : J' ≤ pSpan P := le_pSpan hJ'P
    set l : G := (y : G) with hl
    have hlL : l ∈ L := Subgroup.mem_subgroupOf.mp hy
    have hlJ'P : conjSub l J' ∈ P := hinv J' hJ'P l y.2
    have hlJ'Y : conjSub l J' ≤ pSpan P := le_pSpan hlJ'P
    have hxN' : ∀ k ∈ AE.memBar α h b, (I.φ y)⁻¹ * k * I.φ y ∈ AE.memBar α h b := by
      intro k hk
      have h4 : I.φ y ^ 4 = 1 := by
        rw [← hxo]
        exact pow_orderOf_eq_one _
      have h3 : (I.φ y)⁻¹ = I.φ y * I.φ y * I.φ y := by
        rw [inv_eq_iff_mul_eq_one, ← h4, pow_succ, pow_succ, pow_succ, pow_one]
        simp only [mul_assoc]
      have e : (I.φ y)⁻¹ * k * I.φ y = I.φ y * (I.φ y * (I.φ y * k * (I.φ y)⁻¹) *
          (I.φ y)⁻¹) * (I.φ y)⁻¹ := by
        have e1 : (I.φ y)⁻¹ * k * I.φ y =
            (I.φ y * I.φ y * I.φ y) * k * (I.φ y * I.φ y * I.φ y)⁻¹ := by
          rw [← h3, inv_inv]
        rw [e1]
        group
      rw [e]
      exact hxN _ (hxN _ (hxN k hk))
    have hle : (J'.subgroupOf (pSpan P)).map I.φ ≤ ((conjSub l J').subgroupOf (pSpan P)).map I.φ := by
      rw [hlab]
      intro k hk
      have hk' := hxN' k hk
      rw [← hlab] at hk'
      obtain ⟨j, hj, hjk⟩ := hk'
      refine ⟨y * j * y⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · show l * (j : G) * l⁻¹ ∈ conjSub l J'
        exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hj)
      · rw [map_mul, map_mul, map_inv, hjk]
        group
    have heq := TL4.eq_of_map_le_memBar hΩ h2 hn I.φ hk hJ'Δ (hPΔ hlJ'P) hJ'Y hlJ'Y hlab hle
    have hlN : l ∈ Subgroup.normalizer (J' : Set G) := mem_normalizer_iff_conjSub_eq.mpr heq.symm
    have hl2 : l * l ≠ 1 := by
      intro h1
      have h2' : y * y = 1 := Subtype.ext h1
      have h3 : I.φ y * I.φ y = 1 := by rw [← map_mul, h2', map_one]
      have h4 : orderOf (I.φ y) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
      rw [hxo] at h4
      omega
    obtain ⟨-, Q, hQL, hQnc⟩ := hΩ.omega1 L hL
    obtain ⟨hU, -⟩ := zpowers_mem_USet (P := Δ) hL (h2 L hL) (h8 L hL) ⟨Q, hQL, hQnc⟩ hlL hl2
    obtain ⟨x', -, hx'J⟩ := (hPdef _).mp hJ'P
    have hLJ' : L ≠ J' := by
      intro e
      exact hnc ⟨x', by rw [hx'J, e]⟩
    have hstar : L ∈ omegaStarNbr Δ J' :=
      ⟨hL, hLJ', _, hU, Subgroup.zpowers_le.mpr hlL, Subgroup.zpowers_le.mpr hlN⟩
    have hnbr : L ∈ omegaNbr Δ J' := by
      by_contra hn'
      obtain ⟨⟨z', hz'⟩, -⟩ := hΩ.omega1 J' hJ'Δ
      obtain ⟨g, -, hg⟩ := hA J' hJ'Δ L hstar hn' z' v hz' hv
      exact hnc ⟨g * x', by rw [conjSub_mul, hx'J, hg]⟩
    have hcomm := comm_of_mem_omegaNbr hΩ h2 hJ'Δ hnbr
    rintro _ hk _ ⟨c, hc', rfl⟩
    rw [← hlab] at hk
    obtain ⟨a, ha, rfl⟩ := hk
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hc'))
  exact hc B w hBM hBw hB8 hBnc hT hthinB hi fun y hy => by
    rw [show y = v' from Subtype.ext hy]

theorem false_of_ident_core {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ J ∈ Δ, IsPGroup 2 J) (h8 : ∀ J ∈ Δ, Nat.card J = 8) (hA : ∀ J ∈ Δ, AEmpty Δ J)
    (hodd : classicalInvolutionOddCore G = ⊥) {J L X : Subgroup G} (hJ : J ∈ Δ) (hL : L ∈ Δ)
    (hnc : ¬ ∃ g : G, conjSub g J = L) {v : G} (hv : IsUniqueInvolution L v)
    (hvQ : v ∈ pCore 2 G) (hvJ : v ∉ Subgroup.normalizer (J : Set G))
    (hthin : ∀ x ∈ L, x ∈ pCore 2 G → x = 1 ∨ x = v)
    (hXs : X.IsSubnormal) (hJX : J ≤ X) (hLX : L ≤ X)
    (hspan : pSpan {K | ∃ x ∈ X, conjSub x J = K} = X) {n : ℕ} (hn : 5 ≤ n)
    {𝒜 : Set (Finset (Fin n))} {M : Subgroup (AE.AEQ n)} (hc : ModelTwCore 𝒜 M)
    (I : AEIdentOn {K | ∃ x ∈ X, conjSub x J = K} n 𝒜 M) : False :=
  false_of_ident_core_gen hΩ h2 h8 hA hodd hJ hL hnc hv hvQ hvJ hthin hXs hJX hLX
    (fun _ => Iff.rfl) hspan hn I fun B w h1 h2 h3 h4 h5 h6 h7 _ => hc B w h1 h2 h3 h4 h5 h6 h7

theorem false_of_ident_e29 {Δ : Set (Subgroup G)} (hΩ : HypOmegaGen Δ)
    (h2 : ∀ J ∈ Δ, IsPGroup 2 J) (h8 : ∀ J ∈ Δ, Nat.card J = 8) (hA : ∀ J ∈ Δ, AEmpty Δ J)
    (hodd : classicalInvolutionOddCore G = ⊥) {J L X : Subgroup G} (hJ : J ∈ Δ) (hL : L ∈ Δ)
    (hnc : ¬ ∃ g : G, conjSub g J = L) {v : G} (hv : IsUniqueInvolution L v)
    (hvQ : v ∈ pCore 2 G) (hvJ : v ∉ Subgroup.normalizer (J : Set G))
    (hthin : ∀ x ∈ L, x ∈ pCore 2 G → x = 1 ∨ x = v)
    (hXs : X.IsSubnormal) (hJX : J ≤ X) (hLX : L ≤ X)
    (hspan : pSpan {K | ∃ x ∈ X, conjSub x J = K} = X)
    (hspan' : pSpan {K | ∃ x ∈ X, conjSub x L = K} = X)
    (hZ : ModelCenter AE.e29Sub) (hInv : ModelInvO2 AE.e29Sets AE.e29Sub)
    (hc : ModelTwCoreZ AE.e29Sets AE.e29Sub)
    (I : AEIdentOn {K | ∃ x ∈ X, conjSub x J = K} 8 AE.e29Sets AE.e29Sub)
    (I' : AEIdentOn {K | ∃ x ∈ X, conjSub x L = K} 8 AE.e29Sets AE.e29Sub) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoddX : classicalInvolutionOddCore ↥(pSpan {K | ∃ x ∈ X, conjSub x J = K}) = ⊥ := by
    rw [hspan]
    exact TL4.oddCore_eq_bot_of_isSubnormal hodd hXs
  have hk : IsPGroup 2 I.φ.ker := I.toLabel.isPGroup_ker hoddX
  have hXP : ∀ g ∈ X, g ∈ pSpan {K | ∃ x ∈ X, conjSub x J = K} := fun g hg => by
    rw [hspan]; exact hg
  have hXP' : ∀ g ∈ X, g ∈ pSpan {K | ∃ x ∈ X, conjSub x L = K} := fun g hg => by
    rw [hspan']; exact hg
  have hPX : ∀ g ∈ pSpan {K | ∃ x ∈ X, conjSub x J = K}, g ∈ X := fun g hg => by
    rw [← hspan]; exact hg
  have hP'X : ∀ g ∈ pSpan {K | ∃ x ∈ X, conjSub x L = K}, g ∈ X := fun g hg => by
    rw [← hspan']; exact hg
  have hLP' : L ∈ {K | ∃ x ∈ X, conjSub x L = K} := ⟨1, X.one_mem, conjSub_one L⟩
  obtain ⟨β, hβ, hβ4, b, hlab⟩ := I'.label L hLP'
  let v'' : ↥(pSpan {K | ∃ x ∈ X, conjSub x L = K}) := ⟨v, hXP' v (hLX hv.mem)⟩
  have hv''z : I'.φ v'' = AE.zBar β hβ4 := by
    have hmem : I'.φ v'' ∈ AE.memBar β hβ4 b := by
      rw [← hlab]
      exact ⟨v'', Subgroup.mem_subgroupOf.mpr hv.mem, rfl⟩
    have hsq : I'.φ v'' * I'.φ v'' = 1 := by
      rw [← map_mul, show v'' * v'' = 1 from Subtype.ext hv.sq, map_one]
    rcases AE.eq_of_mem_memBar_mul_self (by norm_num) hmem hsq with h1 | h1
    · exfalso
      have hvc := I'.ker_le h1
      apply hvJ
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun j hj => ?_)
      have := Subgroup.mem_center_iff.mp hvc ⟨j, hXP' j (hJX hj)⟩
      exact congrArg Subtype.val this
    · exact h1
  refine false_of_ident_core_gen hΩ h2 h8 hA hodd hJ hL hnc hv hvQ hvJ hthin hXs hJX hLX
    (fun _ => Iff.rfl) hspan (by norm_num) I
    fun B w hBM hBw hB8 hBnc _ hthinB hi hw => hc B w hBM hBw hB8 hBnc ?_ hthinB hi
  intro T hTM hTn hT2 t ht
  obtain ⟨y, rfl⟩ : ∃ y, I.φ y = t := by
    have := hTM ht
    rw [← I.range_eq] at this
    exact this
  let v' : ↥(pSpan {K | ∃ x ∈ X, conjSub x J = K}) := ⟨v, hXP v (hLX hv.mem)⟩
  have hwv : w = I.φ v' := (hw v' rfl).symm
  let N : Subgroup G := (T.comap I.φ).map (pSpan {K | ∃ x ∈ X, conjSub x J = K}).subtype
  have hNX : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    rintro x hx _ ⟨z, hz, rfl⟩
    refine ⟨⟨x, hXP x hx⟩ * z * ⟨x, hXP x hx⟩⁻¹, ?_, rfl⟩
    show I.φ (⟨x, hXP x hx⟩ * z * ⟨x, hXP x hx⟩⁻¹) ∈ T
    rw [map_mul, map_mul, map_inv]
    exact hTn _ (I.range_eq.le ⟨_, rfl⟩) _ hz
  have hN2 : IsPGroup 2 ↥N := (hT2.comap_of_ker_isPGroup I.φ hk).map _
  have hyN : (y : G) ∈ N := ⟨y, ht, rfl⟩
  let T' : Subgroup (AE.AEQ 8) := (N.subgroupOf (pSpan {K | ∃ x ∈ X, conjSub x L = K})).map I'.φ
  have hT'M : T' ≤ AE.e29Sub := (Subgroup.map_le_range _ _).trans I'.range_eq.le
  have hT'n : ∀ x ∈ AE.e29Sub, ∀ t' ∈ T', x * t' * x⁻¹ ∈ T' := by
    rintro x hx _ ⟨n', hn', rfl⟩
    rw [← I'.range_eq] at hx
    obtain ⟨x', rfl⟩ := hx
    refine ⟨x' * n' * x'⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact hNX _ (hP'X _ x'.2) _ (Subgroup.mem_subgroupOf.mp hn')
  have hT'2 : IsPGroup 2 ↥T' := hN2.comap_subtype.map _
  let g'' : ↥(pSpan {K | ∃ x ∈ X, conjSub x L = K}) := ⟨(y : G), hXP' _ (hPX _ y.2)⟩
  have hcomm' := hInv β hβ hβ4 T' hT'M hT'n hT'2 (I'.φ g'')
    ⟨g'', Subgroup.mem_subgroupOf.mpr hyN, rfl⟩
  rw [← hv''z] at hcomm'
  have hcen : ∀ x ∈ X, x * (v * (y : G) * v⁻¹ * (y : G)⁻¹) =
      (v * (y : G) * v⁻¹ * (y : G)⁻¹) * x := by
    intro x hx
    have h1 : v'' * g'' * v''⁻¹ * g''⁻¹ ∈ I'.φ.ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv]
      rw [hcomm', mul_inv_cancel_right, mul_inv_cancel]
    have h2 := Subgroup.mem_center_iff.mp (I'.ker_le h1) ⟨x, hXP' x hx⟩
    exact congrArg Subtype.val h2
  have hc0 : v' * y * v'⁻¹ * y⁻¹ ∈ Subgroup.center ↥(pSpan {K | ∃ x ∈ X, conjSub x J = K}) := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (hcen _ (hPX _ z.2))
  have hφ1 : I.φ (v' * y * v'⁻¹ * y⁻¹) = 1 := by
    refine hZ _ (I.range_eq.le ⟨_, rfl⟩) fun m' hm' => ?_
    rw [← I.range_eq] at hm'
    obtain ⟨z, rfl⟩ := hm'
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hc0 z).symm]
  rw [hwv]
  simp only [map_mul, map_inv] at hφ1
  calc I.φ v' * I.φ y = I.φ v' * I.φ y * (I.φ v')⁻¹ * (I.φ y)⁻¹ * (I.φ y * I.φ v') := by group
    _ = I.φ y * I.φ v' := by rw [hφ1, one_mul]

theorem thmD1TwAt_of_facts (hF : D1TwFacts) {r : ℕ} (hD2 : ThmDGenBelow r (Nat.card G + 1)) :
    ThmD1TwAt r G := by
  intro Δ hΩ h2 h8 hA hodd hall J hJ L hL hnc
  by_contra hcomm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pCore 2 G).Normal := pCore_normal
  have hTw := twinT4Hyp_of hΩ h2 h8 hA hodd
  obtain ⟨⟨u, hu⟩, -⟩ := hΩ.omega1 J hJ
  obtain ⟨⟨v, hv⟩, -⟩ := hΩ.omega1 L hL
  have hnc' : ¬ ∃ g : G, conjSub g L = J := by
    rintro ⟨g, hg⟩
    exact hnc ⟨g⁻¹, by rw [← hg, conjSub_inv_conjSub]⟩
  have hcomm' : ¬ Commutes L J := fun h => hcomm fun x hx y hy => (h y hy x hx).symm
  have hvJ := not_mem_normalizer_of_not_commutes hTw hJ hL hnc hcomm hu hv (hall J hJ u hu)
    (hall L hL v hv)
  have huL := not_mem_normalizer_of_not_commutes hTw hL hJ hnc' hcomm' hv hu (hall L hL v hv)
    (hall J hJ u hu)
  have hT : ∀ {J₁ L₁ : Subgroup G}, J₁ ∈ Δ → L₁ ∈ Δ → ∀ {v₁ : G}, IsUniqueInvolution L₁ v₁ →
      v₁ ∉ Subgroup.normalizer (J₁ : Set G) →
        ∀ g : G, ∀ U ∈ USet Δ, U ≤ conjSub g J₁ → ¬ U ≤ pCore 2 G := by
    intro J₁ L₁ hJ₁ hL₁ v₁ hv₁ hv₁J g U hU hUJ
    exact not_le_of_not_mem_normalizer hΩ h2 (hΩ.conjInvariant g J₁ hJ₁)
      (hΩ.conjInvariant g L₁ hL₁) (hv₁.conj g) (not_mem_normalizer_conj hv₁J g) pCore_normal
      pCore_isPGroup hU hUJ
  obtain ⟨Y, hY⟩ := exists_d1TwSub hF hΩ h2 h8 hA hodd hall hD2 hJ (hT hJ hL hv hvJ)
  obtain ⟨Y', hY'⟩ := exists_d1TwSub hF hΩ h2 h8 hA hodd hall hD2 hL (hT hL hJ hu huL)
  have hvQ := TL4.mem_pCore_of_tightInO2 (hall L hL v hv)
  have hJL : J ≠ L := fun e => hnc ⟨1, by rw [conjSub_one, e]⟩
  rcases TL4.eq_or_comm_mem_pCore hY.sub hY'.sub hY.pack hY'.pack with heq | hcm
  · subst heq
    have hLY : L ≤ Y := hY'.le
    rcases hY.out with ⟨E, hE⟩ | ⟨hJ8, n, 𝒜, M, hn, hc, ⟨I⟩⟩ | ⟨hJ8, hI29⟩
    ·
      apply hvJ
      refine hY.e8 E hE (hE.core (Y ⊓ pCore 2 G) inf_le_left (fun x hx q hq =>
        ⟨Y.mul_mem (Y.mul_mem hx hq.1) (Y.inv_mem hx), pCore_normal.conj_mem q hq.2 x⟩)
        (pCore_isPGroup.to_le inf_le_right) ⟨hLY hv.mem, hvQ⟩)
    · have h8' : ∀ K ∈ Δ, Nat.card K = 8 := fun K hK => by rw [h8 K hK, ← h8 J hJ, hJ8]
      have hthin : ∀ x ∈ L, x ∈ pCore 2 G → x = 1 ∨ x = v := by
        intro x hx hxQ
        by_contra hne
        push Not at hne
        have hx2 : x * x ≠ 1 := fun h => (hv.unique x hx h).elim hne.1 hne.2
        obtain ⟨-, Q, hQL, hQnc⟩ := hΩ.omega1 L hL
        obtain ⟨hU, -⟩ := zpowers_mem_USet (P := Δ) hL (h2 L hL) (h8' L hL) ⟨Q, hQL, hQnc⟩ hx hx2
        exact hT hL hJ hu huL 1 _ hU (by rw [conjSub_one]; exact Subgroup.zpowers_le.mpr hx)
          (Subgroup.zpowers_le.mpr hxQ)
      exact false_of_ident_core hΩ h2 h8' hA hodd hJ hL hnc hv hvQ hvJ hthin hY.sub hY.le hLY
        hY.span hn hc I
    ·
      have h8' : ∀ K ∈ Δ, Nat.card K = 8 := fun K hK => by rw [h8 K hK, ← h8 J hJ, hJ8]
      have huQ := TL4.mem_pCore_of_tightInO2 (hall J hJ u hu)
      have hJY : J ≤ Y := hY.le
      have hthinOf : ∀ {J₁ L₁ : Subgroup G}, J₁ ∈ Δ → L₁ ∈ Δ → ∀ {u₁ v₁ : G},
          IsUniqueInvolution J₁ u₁ → IsUniqueInvolution L₁ v₁ →
          u₁ ∉ Subgroup.normalizer (L₁ : Set G) → ∀ x ∈ L₁, x ∈ pCore 2 G → x = 1 ∨ x = v₁ := by
        intro J₁ L₁ hJ₁ hL₁ u₁ v₁ hu₁ hv₁ hu₁L x hx hxQ
        by_contra hne
        push Not at hne
        have hx2 : x * x ≠ 1 := fun h => (hv₁.unique x hx h).elim hne.1 hne.2
        obtain ⟨-, Q, hQL, hQnc⟩ := hΩ.omega1 L₁ hL₁
        obtain ⟨hU, -⟩ := zpowers_mem_USet (P := Δ) hL₁ (h2 L₁ hL₁) (h8' L₁ hL₁) ⟨Q, hQL, hQnc⟩
          hx hx2
        exact hT hL₁ hJ₁ hu₁ hu₁L 1 _ hU (by rw [conjSub_one]; exact Subgroup.zpowers_le.mpr hx)
          (Subgroup.zpowers_le.mpr hxQ)
      have hthinL := hthinOf hJ hL hu hv huL
      have hthinJ := hthinOf hL hJ hv hu hvJ
      rcases hY'.out with ⟨E, hE⟩ | ⟨-, m, 𝒜', M', hm, hc', ⟨I'⟩⟩ | ⟨-, ⟨I'⟩⟩
      ·
        apply huL
        exact hY'.e8 E hE (hE.core (Y ⊓ pCore 2 G) inf_le_left (fun x hx q hq =>
          ⟨Y.mul_mem (Y.mul_mem hx hq.1) (Y.inv_mem hx), pCore_normal.conj_mem q hq.2 x⟩)
          (pCore_isPGroup.to_le inf_le_right) ⟨hJY hu.mem, huQ⟩)
      · exact false_of_ident_core hΩ h2 h8' hA hodd hL hJ hnc' hu huQ huL hthinJ hY.sub hLY hJY
          hY'.span hm hc' I'
      · obtain ⟨I⟩ := hI29
        exact false_of_ident_e29 hΩ h2 h8' hA hodd hJ hL hnc hv hvQ hvJ hthinL hY.sub hJY hLY
          hY.span hY'.span hF.e29Center hF.e29Inv hF.e29CoreZ I I'
  ·
    apply hcomm
    have hJQ2 : IsPGroup 2 ↥(J ⊔ pCore 2 G) :=
      IsPGroup.to_sup_of_normal_right (h2 J hJ) pCore_isPGroup
    have hconj : ∀ l ∈ L, ∀ x ∈ J ⊔ pCore 2 G, l * x * l⁻¹ ∈ J ⊔ pCore 2 G := by
      intro l hl x hx
      have hle : J ⊔ pCore 2 G ≤ (J ⊔ pCore 2 G).comap (MulAut.conj l).toMonoidHom := by
        refine sup_le (fun j hj => ?_) (fun q hq => ?_)
        · show l * j * l⁻¹ ∈ J ⊔ pCore 2 G
          have hc := hcm j (hY.le hj) l (hY'.le hl)
          have e : l * j * l⁻¹ = (j * l * j⁻¹ * l⁻¹)⁻¹ * j := by group
          rw [e]
          exact (J ⊔ pCore 2 G).mul_mem (Subgroup.mem_sup_right ((pCore 2 G).inv_mem hc))
            (Subgroup.mem_sup_left hj)
        · show l * q * l⁻¹ ∈ J ⊔ pCore 2 G
          exact Subgroup.mem_sup_right (pCore_normal.conj_mem q hq l)
      exact hle hx
    have hLN : L ≤ Subgroup.normalizer ((J ⊔ pCore 2 G : Subgroup G) : Set G) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨hconj l hl x, fun h => ?_⟩
      have := hconj l⁻¹ (L.inv_mem hl) _ h
      simpa [mul_assoc] using this
    have h2grp := IsPGroup.to_sup_of_normal_left' hJQ2 (h2 L hL) hLN
    exact TL4.commutes_of_le_two hΩ h2 hJ hL hJL h2grp (le_sup_left.trans le_sup_left)
      le_sup_right

theorem ThmDGenBelow.mono {r m n : ℕ} (h : ThmDGenBelow r n) (hmn : m ≤ n) :
    ThmDGenBelow r m :=
  fun G _ _ Ω hΩ h2 h8 hA P hPΩ hcard => h G Ω hΩ h2 h8 hA P hPΩ (lt_of_lt_of_le hcard hmn)

theorem d1GenLeaf_of_facts (hF : D1TwFacts) (r : ℕ) : D1GenLeaf r := by
  intro n hD2
  refine thmD1GenBelow_of_twAt fun H _ _ hH => thmD1TwAt_of_facts hF (hD2.mono (by omega))


variable {r : ℕ} {IH : ℕ → Prop}

theorem dLeafC_of₃ (hF : D1TwFacts) (hE8 : CLeafE8 r IH) (hE64 : CLeafE64 r IH)
    (hE29 : CLeafE29 r IH) (hAE : CLeafAE r IH) : DLeafC r IH :=
  dLeafC_of₂ (d1GenLeaf_of_facts hF r) hE8 hE64 hE29 hAE

theorem thmDAbs_of_leaves₆ (hF : D1TwFacts) (hE8 : CLeafE8 r IH) (hE64 : CLeafE64 r IH)
    (hE29 : CLeafE29 r IH) (hAE : CLeafAE r IH) (hE4 : DLeafE4 r IH) (hstar : DLeafStar r IH)
    (hend : DLeafEnd r IH) (hih : ∀ n, IH n) : ThmDAbs r :=
  thmDAbs_of_leaves₅ (d1GenLeaf_of_facts hF r) hE8 hE64 hE29 hAE hE4 hstar hend hih

section Cit3


theorem thmD2Step_of_leaves₅ (hF : D1TwFacts) (hE8 : CLeafE8 r (PackIH r))
    (hE64 : CLeafE64 r (PackIH r)) (hE29 : CLeafE29 r (PackIH r)) (hAE : CLeafAE r (PackIH r))
    (hE4 : DLeafE4 r (PackIH r)) (hstar : DLeafStar r (PackIH r)) (hend : DLeafEnd r (PackIH r))
    (n : ℕ) : CIT3Below n → TL4.TightBelowRPlus r n → ThmDAbsBelow r (n + 1) :=
  thmD2Step_of_leaves₄ (d1GenLeaf_of_facts hF r) hE8 hE64 hE29 hAE hE4 hstar hend n

end Cit3

end CFSG.ClassicalInvolution.Q3.TC.Thin
