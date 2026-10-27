module

public import Mathlib.GroupTheory.NoncommCoprod
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Prelude
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup CFSG.GH74.GLS.Stage1.Thm6

variable {G : Type*} [Group G]

@[simp] theorem mem_Hconj {g a : G} {H : Subgroup G} : a ∈ Hconj g H ↔ g * a * g⁻¹ ∈ H := Iff.rfl

theorem Hconj_mul (g h : G) (H : Subgroup G) : Hconj g (Hconj h H) = Hconj (h * g) H := by
  ext a; simp [mul_assoc]

theorem Hconj_one (H : Subgroup G) : Hconj 1 H = H := by ext a; simp

theorem Hconj_inv_Hconj (g : G) (H : Subgroup G) : Hconj g⁻¹ (Hconj g H) = H := by
  rw [Hconj_mul]; simp [Hconj_one]

theorem Hconj_Hconj_inv (g : G) (H : Subgroup G) : Hconj g (Hconj g⁻¹ H) = H := by
  rw [Hconj_mul]; simp [Hconj_one]

theorem Hconj_card (g : G) (H : Subgroup G) : Nat.card (Hconj g H) = Nat.card H :=
  Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv (by intro a; simp [Hconj]))

theorem Hconj_le_Hconj {g : G} {H K : Subgroup G} (h : H ≤ K) : Hconj g H ≤ Hconj g K :=
  fun _ ha => h ha

theorem Hconj_inf (g : G) (H K : Subgroup G) : Hconj g (H ⊓ K) = Hconj g H ⊓ Hconj g K := by
  ext a; simp

theorem Hconj_centralizer (g x : G) :
    Hconj g (Subgroup.centralizer ({x} : Set G)) = Subgroup.centralizer ({g⁻¹ * x * g} : Set G) := by
  ext a
  simp only [mem_Hconj, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have : g⁻¹ * x * g * a = a * (g⁻¹ * x * g) := by
      have h' : x * (g * a * g⁻¹) = g * a * g⁻¹ * x := h
      calc g⁻¹ * x * g * a = g⁻¹ * (x * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * a * g⁻¹ * x) * g := by rw [h']
        _ = a * (g⁻¹ * x * g) := by group
    exact this
  · intro h
    have h' : g⁻¹ * x * g * a = a * (g⁻¹ * x * g) := h
    calc x * (g * a * g⁻¹) = g * (g⁻¹ * x * g * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by rw [h']
      _ = g * a * g⁻¹ * x := by group

theorem IsElemAb2.mono {E F : Subgroup G} (h : IsElemAb2 E) (hFE : F ≤ E) : IsElemAb2 F :=
  fun a ha => ⟨(h a (hFE ha)).1, fun b hb => (h a (hFE ha)).2 b (hFE hb)⟩

theorem IsElemAb2.hconj {E : Subgroup G} (h : IsElemAb2 E) (g : G) : IsElemAb2 (Hconj g E) := by
  intro a ha
  have h1 := (h _ ha).1
  refine ⟨?_, fun b hb => ?_⟩
  · have : g * (a * a) * g⁻¹ = 1 := by simpa [mul_assoc] using h1
    simpa using this
  · have h2 := (h _ ha).2 _ hb
    have : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h2
        _ = g * (b * a) * g⁻¹ := by group
    simpa using this

theorem mem_sup_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {y : G}
    (hy : y ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have hnorm : A ≤ Subgroup.normalizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have : a * b * a⁻¹ = b := by rw [hc a ha b hb]; group
      rwa [this]
    · intro hb
      have h1 := hc a ha _ hb
      have : a * b * a⁻¹ = b := by
        calc a * b * a⁻¹ = a⁻¹ * (a * (a * b * a⁻¹)) := by group
          _ = a⁻¹ * ((a * b * a⁻¹) * a) := by rw [h1]
          _ = b := by group
      rwa [this] at hb
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hnorm
  have hy' : y ∈ (↑(A ⊔ B) : Set G) := hy
  rw [hset] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hy'
  exact ⟨a, ha, b, hb, rfl⟩

theorem card_sup_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hd : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype hcomm) := by
    refine (MonoidHom.noncommCoprod_injective A.subtype B.subtype hcomm).2 ?_
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hd
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  calc Nat.card ↥(A ⊔ B) = Nat.card (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range := by
        rw [hrange]
    _ = Nat.card (↥A × ↥B) := (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

theorem IsElemAb2.sup {A B : Subgroup G} (hA : IsElemAb2 A) (hB : IsElemAb2 B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsElemAb2 (A ⊔ B) := by
  have key : ∀ y ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, y = a * b := fun y hy => mem_sup_of_commute hc hy
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := key y hy
  refine ⟨?_, fun y' hy' => ?_⟩
  · have hba : Commute b a := (hc a ha b hb).symm
    rw [hba.mul_mul_mul_comm a b]
    rw [(hA a ha).1, (hB b hb).1, one_mul]
  · obtain ⟨a', ha', b', hb', rfl⟩ := key y' hy'
    have hac : Commute a a' := (hA a ha).2 a' ha'
    have had : Commute a b' := hc a ha b' hb'
    have hbc : Commute b a' := (hc a' ha' b hb).symm
    have hbd : Commute b b' := (hB b hb).2 b' hb'
    exact (hac.mul_right had).mul_left (hbc.mul_right hbd)

theorem isElemAb2_zpowers {x : G} (hx : x * x = 1) : IsElemAb2 (Subgroup.zpowers x) := by
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  intro a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  refine ⟨?_, fun b hb => ?_⟩
  · rw [← zpow_add, ← two_mul, zpow_mul, hx2, one_zpow]
  · obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (zpow_mul_comm x k l)

theorem card_zpowers_of_sq {x : G} (hx : x * x = 1) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.zpowers x) = 2 := by
  have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime hx2 hx1

noncomputable def sylow2ToSylow {P H : Subgroup G} (h : IsSylow2In P H) : Sylow 2 ↥H :=
  (h.2.1.comap_subtype (K := H)).toSylow h.2.2

theorem coe_sylow2ToSylow {P H : Subgroup G} (h : IsSylow2In P H) :
    ((sylow2ToSylow h : Subgroup ↥H)) = P.subgroupOf H := by
  unfold sylow2ToSylow
  exact IsPGroup.toSylow_coe _ _

theorem mem_sylow2ToSylow {P H : Subgroup G} (h : IsSylow2In P H) {a : G} (ha : a ∈ H) :
    a ∈ P ↔ (⟨a, ha⟩ : ↥H) ∈ (sylow2ToSylow h : Subgroup ↥H) := by
  rw [coe_sylow2ToSylow]
  rfl

theorem sylow2_conj {P H : Subgroup G} (h : IsSylow2In P H) (g : G) :
    IsSylow2In (Hconj g P) (Hconj g H) := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hsurj : Function.Surjective (MulAut.conj g).toMonoidHom := (MulAut.conj g).surjective
  refine ⟨fun a ha => h.1 ha, h.2.1.comap_of_injective _ hinj, ?_⟩
  have : (Hconj g P).relIndex (Hconj g H) = P.relIndex H := by
    unfold Hconj
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hsurj]
  rw [this]
  exact h.2.2

theorem sylow2_exists_conj [Finite G] {P₁ P₂ H : Subgroup G} (h₁ : IsSylow2In P₁ H)
    (h₂ : IsSylow2In P₂ H) : ∃ c ∈ H, P₂ = Hconj c P₁ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) (sylow2ToSylow h₁) (sylow2ToSylow h₂)
  refine ⟨((g⁻¹ : ↥H) : G), (g⁻¹ : ↥H).2, ?_⟩
  ext a
  have hc : ∀ a : G, (((g⁻¹ : ↥H) : G) * a * ((g⁻¹ : ↥H) : G)⁻¹ ∈ P₁ → a ∈ H) := by
    intro a ha
    have h1 : ((g⁻¹ : ↥H) : G) * a * ((g⁻¹ : ↥H) : G)⁻¹ ∈ H := h₁.1 ha
    have := H.mul_mem (H.mul_mem (H.inv_mem (g⁻¹ : ↥H).2) h1) (g⁻¹ : ↥H).2
    simpa [mul_assoc] using this
  by_cases ha : a ∈ H
  · rw [mem_Hconj, mem_sylow2ToSylow h₂ ha, ← hg, Sylow.coe_subgroup_smul,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h1 : ((g⁻¹ : ↥H) : G) * a * ((g⁻¹ : ↥H) : G)⁻¹ ∈ H := by
      exact H.mul_mem (H.mul_mem (g⁻¹ : ↥H).2 ha) (H.inv_mem (g⁻¹ : ↥H).2)
    rw [mem_sylow2ToSylow h₁ h1]
    simp
    exact Iff.rfl
  · constructor
    · intro h; exact absurd (h₂.1 h) ha
    · intro h; exact absurd (hc a h) ha

theorem sylow2_card_eq [Finite G] {P₁ P₂ H : Subgroup G} (h₁ : IsSylow2In P₁ H)
    (h₂ : IsSylow2In P₂ H) : Nat.card P₁ = Nat.card P₂ := by
  obtain ⟨c, _, hc⟩ := sylow2_exists_conj h₁ h₂
  rw [hc, Hconj_card]

theorem sylow2_eq_of_le [Finite G] {P H Q : Subgroup G} (h : IsSylow2In P H) (hQ : IsPGroup 2 ↥Q)
    (hPQ : P ≤ Q) (hQH : Q ≤ H) : Q = P := by
  have key := (sylow2ToSylow h).is_maximal' (Q := Q.subgroupOf H) (hQ.comap_subtype (K := H))
    (by rw [coe_sylow2ToSylow h]; exact fun a ha => hPQ ha)
  rw [coe_sylow2ToSylow] at key
  have := Subgroup.subgroupOf_inj.1 key
  rwa [inf_eq_left.2 hQH, inf_eq_left.2 h.1] at this

theorem exists_sylow2_ge [Finite G] {A H : Subgroup G} (hA : IsPGroup 2 ↥A) (hAH : A ≤ H) :
    ∃ P : Subgroup G, IsSylow2In P H ∧ A ≤ P := by
  obtain ⟨Sy, hSy⟩ := (hA.comap_subtype (K := H)).exists_le_sylow
  refine ⟨(Sy : Subgroup ↥H).map H.subtype, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a ha
    obtain ⟨b, _, rfl⟩ := ha
    exact b.2
  · exact Sy.isPGroup'.map H.subtype
  · have hs : ((Sy : Subgroup ↥H).map H.subtype).relIndex H = (Sy : Subgroup ↥H).index := by
      unfold Subgroup.relIndex Subgroup.subgroupOf
      rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [hs]
    exact Sylow.not_dvd_index Sy
  · intro a ha
    have : (⟨a, hAH ha⟩ : ↥H) ∈ A.subgroupOf H := ha
    exact ⟨_, hSy this, rfl⟩

theorem exists_mem_normalizer_of_lt [Finite G] {S T : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hTS : T < S) :
    ∃ a ∈ S, a ∉ T ∧ ∀ t : G, t ∈ T ↔ a * t * a⁻¹ ∈ T := by
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  have hcond := Group.normalizerCondition_of_isNilpotent (G := ↥S)
  have hlt : T.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact absurd hTS (not_lt_of_ge h)
  obtain ⟨a, ha, haT⟩ := IsConcreteLE.exists_of_lt (hcond _ hlt)
  rw [Subgroup.mem_normalizer_iff] at ha
  refine ⟨a, a.2, haT, fun t => ?_⟩
  by_cases htS : t ∈ S
  · exact ha ⟨t, htS⟩
  · constructor
    · intro ht; exact absurd (hTS.le ht) htS
    · intro ht
      exfalso
      apply htS
      have h1 : (a : G) * t * (a : G)⁻¹ ∈ S := hTS.le ht
      have := S.mul_mem (S.mul_mem (S.inv_mem a.2) h1) a.2
      simpa [mul_assoc] using this

theorem exists_central_involution_of_normal [Finite G] {T N : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTN : N ≤ T) (hnorm : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) (hne : N ≠ ⊥) :
    ∃ u ∈ N, u ≠ 1 ∧ u * u = 1 ∧ ∀ t ∈ T, u * t = t * u := by
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hN' : (N.subgroupOf T).Normal := by
    refine ⟨fun n hn g => ?_⟩
    show ((g * n * g⁻¹ : ↥T) : G) ∈ N
    have := hnorm (g : G) g.2 (n : G) hn
    simpa using this
  have hne' : N.subgroupOf T ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hTN ha⟩ : ↥T) ∈ N.subgroupOf T := ha
    rw [h] at this
    have h2 : (⟨a, hTN ha⟩ : ↥T) = 1 := this
    have : a = 1 := congrArg Subtype.val h2
    simp [this]
  have hM := Group.IsNilpotent.inf_center_ne_bot_of_normal hne'
  set M : Subgroup ↥T := N.subgroupOf T ⊓ Subgroup.center ↥T with hMdef
  have hMp : IsPGroup 2 ↥M := hT.to_subgroup M
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hMp
  have hn1 : n ≠ 0 := by
    rintro rfl
    exact hM (Subgroup.eq_bot_of_card_eq M (by simpa using hn))
  have hdvd : 2 ∣ Nat.card ↥M := by rw [hn]; exact dvd_pow_self 2 hn1
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hyM : (y : ↥T) ∈ M := y.2
  have hyN : (y : ↥T) ∈ N.subgroupOf T := hyM.1
  have hyC : (y : ↥T) ∈ Subgroup.center ↥T := hyM.2
  refine ⟨((y : ↥T) : G), hyN, ?_, ?_, ?_⟩
  · intro h
    have h1 : (y : ↥T) = 1 := Subtype.ext h
    have h2 : y = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hy
    omega
  · have h1 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    have h2 : ((y : ↥T) : G) ^ 2 = 1 := by
      have := congrArg (fun z : ↥M => ((z : ↥T) : G)) h1
      simpa using this
    simpa [pow_two] using h2
  · intro t ht
    have := (Subgroup.mem_center_iff.1 hyC) ⟨t, ht⟩
    exact (congrArg Subtype.val this).symm

theorem exists_involution_of_ne_bot [Finite G] {N : Subgroup G} (hN : IsPGroup 2 ↥N)
    (hne : N ≠ ⊥) : ∃ y ∈ N, y ≠ 1 ∧ y * y = 1 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hN
  have hn1 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq N (by simpa using hn))
  have hdvd : 2 ∣ Nat.card ↥N := by rw [hn]; exact dvd_pow_self 2 hn1
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨(y : G), y.2, ?_, ?_⟩
  · intro h
    have h2 : y = 1 := Subtype.ext h
    rw [h2, orderOf_one] at hy
    omega
  · have h1 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    have := congrArg (fun z : ↥N => (z : G)) h1
    simpa [pow_two] using this

end CFSG.GH74.GLS.Stage1.Thm6.Sec12
