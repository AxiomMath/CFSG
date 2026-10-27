module

public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Data

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Omnibus

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G]

section Products

theorem coe_sup_of_mul_comm {A B : Subgroup G} (h : (A : Set G) * B = B * A) :
    ((A ⊔ B : Subgroup G) : Set G) = A * B := by
  let S : Subgroup G :=
    { carrier := (A : Set G) * B
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        have hba : b * a' ∈ (B : Set G) * A := ⟨b, hb, a', ha', rfl⟩
        rw [← h] at hba
        obtain ⟨a'', ha'', b'', hb'', he⟩ := hba
        refine ⟨a * a'', A.mul_mem ha ha'', b'' * b', B.mul_mem hb'' hb', ?_⟩
        change a * a'' * (b'' * b') = a * b * (a' * b')
        rw [show a * b * (a' * b') = a * (b * a') * b' by group, ← he]
        group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have hba : b⁻¹ * a⁻¹ ∈ (B : Set G) * A := ⟨b⁻¹, B.inv_mem hb, a⁻¹, A.inv_mem ha, rfl⟩
        rw [← h] at hba
        change (a * b)⁻¹ ∈ (A : Set G) * B
        rwa [mul_inv_rev] }
  have hAS : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩
  have hBS : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩
  apply Set.Subset.antisymm
  · exact sup_le hAS hBS
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem mem_sup_of_mul_comm {A B : Subgroup G} (h : (A : Set G) * B = B * A) {g : G}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  have hg' : g ∈ ((A ⊔ B : Subgroup G) : Set G) := hg
  rw [coe_sup_of_mul_comm h] at hg'
  obtain ⟨a, ha, b, hb, he⟩ := hg'
  exact ⟨a, ha, b, hb, he⟩

theorem mem_sup_of_mul_comm' {A B : Subgroup G} (h : (A : Set G) * B = B * A) {g : G}
    (hg : g ∈ A ⊔ B) : ∃ b ∈ B, ∃ a ∈ A, b * a = g := by
  have hg' : g ∈ ((A ⊔ B : Subgroup G) : Set G) := hg
  rw [coe_sup_of_mul_comm h, h] at hg'
  obtain ⟨b, hb, a, ha, he⟩ := hg'
  exact ⟨b, hb, a, ha, he⟩

theorem mul_comm_of_le_normalizer {A B : Subgroup G} (h : A ≤ Subgroup.normalizer (B : Set G)) :
    (A : Set G) * B = B * A :=
  Subgroup.set_mul_normalizer_comm _ _ h

theorem relIndex_sup_of_mul_comm {A B : Subgroup G} (h : (A : Set G) * B = B * A) :
    B.relIndex (A ⊔ B) = B.relIndex A := by
  classical
  set K : Subgroup G := A ⊔ B with hK
  let incl : A → K := fun a => ⟨a, (le_sup_left : A ≤ K) a.2⟩
  let f : A ⧸ B.subgroupOf A → K ⧸ B.subgroupOf K :=
    Quotient.map' incl (by
      intro a a' haa
      rw [QuotientGroup.leftRel_apply] at haa ⊢
      exact haa)
  have hinj : Function.Injective f := by
    intro u v huv
    induction u using QuotientGroup.induction_on with | H a => ?_
    induction v using QuotientGroup.induction_on with | H a' => ?_
    have huv' : (QuotientGroup.mk (incl a) : K ⧸ B.subgroupOf K) = QuotientGroup.mk (incl a') :=
      huv
    rw [QuotientGroup.eq] at huv' ⊢
    exact huv'
  have hsurj : Function.Surjective f := by
    intro w
    induction w using QuotientGroup.induction_on with | H k => ?_
    obtain ⟨a, ha, b, hb, he⟩ := mem_sup_of_mul_comm h k.2
    refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
    change (QuotientGroup.mk (incl ⟨a, ha⟩) : K ⧸ B.subgroupOf K) = QuotientGroup.mk k
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (a : G)⁻¹ * k ∈ B
    rw [← he]
    simpa using hb
  exact (Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩).symm

theorem inf_mul_comm_of_le {U C N : Subgroup G} (hCN : C ≤ N) (h : (U : Set G) * C = C * U) :
    ((U ⊓ N : Subgroup G) : Set G) * C = C * (U ⊓ N : Subgroup G) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, hv, c, hc, rfl⟩
    have hmem : v * c ∈ (C : Set G) * U := by rw [← h]; exact ⟨v, hv.1, c, hc, rfl⟩
    obtain ⟨c', hc', u, hu, he⟩ := hmem
    refine ⟨c', hc', u, ⟨hu, ?_⟩, he⟩
    have : u = c'⁻¹ * (v * c) := by rw [← he]; group
    rw [this]
    exact N.mul_mem (N.inv_mem (hCN hc')) (N.mul_mem hv.2 (hCN hc))
  · rintro _ ⟨c, hc, v, hv, rfl⟩
    have hmem : c * v ∈ (U : Set G) * C := by rw [h]; exact ⟨c, hc, v, hv.1, rfl⟩
    obtain ⟨u, hu, c', hc', he⟩ := hmem
    refine ⟨u, ⟨hu, ?_⟩, c', hc', he⟩
    have : u = c * v * c'⁻¹ := by rw [← he]; group
    rw [this]
    exact N.mul_mem (N.mul_mem (hCN hc) hv.2) (N.inv_mem (hCN hc'))

theorem mul_comm_of_le_of_le_sup {U V C : Subgroup G} (h : (U : Set G) * C = C * U)
    (hUV : U ≤ V) (hV : V ≤ U ⊔ C) : (V : Set G) * C = C * V := by
  have hX : ((U ⊔ C : Subgroup G) : Set G) = U * C := coe_sup_of_mul_comm h
  have h1 : (V : Set G) * C = ((U ⊔ C : Subgroup G) : Set G) := by
    apply Set.Subset.antisymm
    · exact Subgroup.mul_subset hV (SetLike.coe_subset_coe.mpr le_sup_right)
    · rw [hX]
      exact Set.mul_subset_mul_right hUV
  have h2 : (C : Set G) * V = ((U ⊔ C : Subgroup G) : Set G) := by
    apply Set.Subset.antisymm
    · exact Subgroup.mul_subset (SetLike.coe_subset_coe.mpr le_sup_right) hV
    · rw [hX, h]
      exact Set.mul_subset_mul_left hUV
  rw [h1, h2]

end Products

section ConjSub

theorem mem_conjSub {g x : G} {X : Subgroup G} : x ∈ conjSub g X ↔ g⁻¹ * x * g ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem conj_mem_conjSub {g x : G} {X : Subgroup G} (hx : x ∈ X) : g * x * g⁻¹ ∈ conjSub g X :=
  ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem conjSub_mul (g h : G) (X : Subgroup G) :
    conjSub (g * h) X = conjSub g (conjSub h X) := by
  ext x
  simp only [mem_conjSub]
  rw [show (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h by group]

@[simp] theorem conjSub_one (X : Subgroup G) : conjSub 1 X = X := by
  ext x
  simp [mem_conjSub]

theorem conjSub_inv_conjSub (g : G) (X : Subgroup G) : conjSub g⁻¹ (conjSub g X) = X := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv (g : G) (X : Subgroup G) : conjSub g (conjSub g⁻¹ X) = X := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_mono {g : G} {X Y : Subgroup G} (h : X ≤ Y) : conjSub g X ≤ conjSub g Y :=
  Subgroup.map_mono h

theorem conjSub_le_conjSub_iff {g : G} {X Y : Subgroup G} : conjSub g X ≤ conjSub g Y ↔ X ≤ Y := by
  refine ⟨fun h => ?_, conjSub_mono⟩
  have := conjSub_mono (g := g⁻¹) h
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

theorem conjSub_le_iff {g : G} {X Y : Subgroup G} : conjSub g X ≤ Y ↔ X ≤ conjSub g⁻¹ Y := by
  rw [← conjSub_le_conjSub_iff (g := g⁻¹), conjSub_inv_conjSub]

theorem conjSub_inf (g : G) (X Y : Subgroup G) :
    conjSub g (X ⊓ Y) = conjSub g X ⊓ conjSub g Y :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective

theorem conjSub_sup (g : G) (X Y : Subgroup G) :
    conjSub g (X ⊔ Y) = conjSub g X ⊔ conjSub g Y :=
  Subgroup.map_sup _ _ _

@[simp] theorem conjSub_bot (g : G) : conjSub g (⊥ : Subgroup G) = ⊥ :=
  Subgroup.map_bot _

theorem conjSub_eq_bot_iff {g : G} {X : Subgroup G} : conjSub g X = ⊥ ↔ X = ⊥ := by
  refine ⟨fun h => ?_, fun h => by rw [h, conjSub_bot]⟩
  rw [← conjSub_inv_conjSub g X, h, conjSub_bot]

theorem card_conjSub (g : G) (X : Subgroup G) : Nat.card (conjSub g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isPGroup_conjSub {p : ℕ} {g : G} {X : Subgroup G} (h : IsPGroup p X) :
    IsPGroup p (conjSub g X) :=
  h.map _

theorem conjSub_eq_self {g : G} {X : Subgroup G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    conjSub g X = X := by
  ext x
  rw [mem_conjSub, Subgroup.mem_normalizer_iff''.mp hg x]

theorem mem_normalizer_of_conjSub_eq {g : G} {X : Subgroup G} (h : conjSub g X = X) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact conj_mem_conjSub hx
  · intro hx
    rw [← h, mem_conjSub] at hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at hx

theorem mem_normalizer_sup {g : G} {A B : Subgroup G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  mem_normalizer_of_conjSub_eq (by rw [conjSub_sup, conjSub_eq_self hA, conjSub_eq_self hB])

theorem conjSub_eq_self_of_mem {g : G} {X : Subgroup G} (hg : g ∈ X) : conjSub g X = X :=
  conjSub_eq_self (Subgroup.le_normalizer hg)

theorem conjSub_centralizer (g x : G) :
    conjSub g (Subgroup.centralizer ({x} : Set G)) =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  ext y
  rw [mem_conjSub, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * (g * x * g⁻¹) = g * (g⁻¹ * y * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * y := by group
  · intro h
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g) := by group

theorem conj_mem_normalizer_conjSub {g h : G} {X : Subgroup G}
    (hh : h ∈ Subgroup.normalizer (X : Set G)) :
    g * h * g⁻¹ ∈ Subgroup.normalizer ((conjSub g X : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  rw [mem_conjSub, mem_conjSub, Subgroup.mem_normalizer_iff''.mp hh (g⁻¹ * y * g)]
  rw [show (g * h * g⁻¹)⁻¹ * y * (g * h * g⁻¹) = g * (h⁻¹ * (g⁻¹ * y * g) * h) * g⁻¹ by group]
  rw [show g⁻¹ * (g * (h⁻¹ * (g⁻¹ * y * g) * h) * g⁻¹) * g = h⁻¹ * (g⁻¹ * y * g) * h by group]

theorem le_normalizer_conjSub {g : G} {T X : Subgroup G}
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hg : g ∈ Subgroup.normalizer (T : Set G)) :
    T ≤ Subgroup.normalizer ((conjSub g X : Subgroup G) : Set G) := by
  intro t ht
  have ht' : g⁻¹ * t * g ∈ T := (Subgroup.mem_normalizer_iff''.mp hg t).mp ht
  have := conj_mem_normalizer_conjSub (g := g) (hTX ht')
  rwa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at this

theorem conjSub_mul_comm {g : G} {X C : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) (h : (X : Set G) * C = C * X) :
    ((conjSub g X : Subgroup G) : Set G) * C = C * (conjSub g X : Subgroup G) := by
  have key : ∀ {A B : Subgroup G}, (A : Set G) * B ⊆ B * A → g ∈ Subgroup.normalizer (B : Set G) →
      ((conjSub g A : Subgroup G) : Set G) * B ⊆ B * (conjSub g A : Subgroup G) := by
    intro A B hAB hgB
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [SetLike.mem_coe, mem_conjSub] at ha
    have hb' : g⁻¹ * b * g ∈ B := (Subgroup.mem_normalizer_iff''.mp hgB b).mp hb
    obtain ⟨b'', hb'', a'', ha'', he⟩ := hAB ⟨_, ha, _, hb', rfl⟩
    refine ⟨g * b'' * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgB b'').mp hb'',
      g * a'' * g⁻¹, conj_mem_conjSub ha'', ?_⟩
    have he' : b'' * a'' = g⁻¹ * a * g * (g⁻¹ * b * g) := he
    change g * b'' * g⁻¹ * (g * a'' * g⁻¹) = a * b
    rw [show g * b'' * g⁻¹ * (g * a'' * g⁻¹) = g * (b'' * a'') * g⁻¹ by group, he']
    group
  have key' : ∀ {A B : Subgroup G}, (B : Set G) * A ⊆ A * B → g ∈ Subgroup.normalizer (B : Set G) →
      (B : Set G) * (conjSub g A : Subgroup G) ⊆ ((conjSub g A : Subgroup G) : Set G) * B := by
    intro A B hAB hgB
    rintro _ ⟨b, hb, a, ha, rfl⟩
    rw [SetLike.mem_coe, mem_conjSub] at ha
    have hb' : g⁻¹ * b * g ∈ B := (Subgroup.mem_normalizer_iff''.mp hgB b).mp hb
    obtain ⟨a'', ha'', b'', hb'', he⟩ := hAB ⟨_, hb', _, ha, rfl⟩
    refine ⟨g * a'' * g⁻¹, conj_mem_conjSub ha'', g * b'' * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp hgB b'').mp hb'', ?_⟩
    have he' : a'' * b'' = g⁻¹ * b * g * (g⁻¹ * a * g) := he
    change g * a'' * g⁻¹ * (g * b'' * g⁻¹) = b * a
    rw [show g * a'' * g⁻¹ * (g * b'' * g⁻¹) = g * (a'' * b'') * g⁻¹ by group, he']
    group
  exact Set.Subset.antisymm (key h.subset hg) (key' h.symm.subset hg)

theorem isSylowOf_conjSub [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G} (g : G)
    (h : IsSylowOf p P K) : IsSylowOf p (conjSub g P) (conjSub g K) := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  refine ⟨conjSub_mono hle, isPGroup_conjSub hP, ?_⟩
  have hker : (MulAut.conj g).toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj g).injective
  rwa [TotallyInverted.conjSub, TotallyInverted.conjSub, Subgroup.relIndex_map_map, hker,
    sup_bot_eq, sup_bot_eq]

theorem exists_le_conjSub_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {P K Q : Subgroup G}
    (hP : IsSylowOf p P K) (hQK : Q ≤ K) (hQ : IsPGroup p Q) :
    ∃ k ∈ K, Q ≤ conjSub k P := by
  obtain ⟨S, rfl⟩ := hP
  obtain ⟨S', hS'⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S S'
  refine ⟨k, k.2, fun q hq => ?_⟩
  have hq' : (⟨q, hQK hq⟩ : K) ∈ (S' : Subgroup K) := hS' hq
  rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq'
  rw [mem_conjSub]
  refine ⟨_, hq', ?_⟩
  simp [MulAut.inv_apply]

theorem exists_conjSub_eq_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {P Q K : Subgroup G}
    (hP : IsSylowOf p P K) (hQ : IsSylowOf p Q K) : ∃ k ∈ K, conjSub k P = Q := by
  obtain ⟨k, hk, hle⟩ := exists_le_conjSub_of_isSylowOf hP hQ.le hQ.isPGroup
  refine ⟨k, hk, ?_⟩
  have hsyl : IsSylowOf p (conjSub k P) K := by
    have := isSylowOf_conjSub k hP
    rwa [conjSub_eq_self_of_mem hk] at this
  exact (hQ.eq_of_le hle hsyl.le hsyl.isPGroup)

end ConjSub

section Cores

theorem oddCore_map_mulEquiv' {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) : (CFSG.oddCore X).map e.toMonoidHom = CFSG.oddCore Y := by
  apply le_antisymm
  · exact le_sSup ⟨(CFSG.oddCore_normal X).map _ e.surjective,
      by rw [Subgroup.card_map_of_injective e.injective]; exact odd_card_oddCore X⟩
  · have hle : (CFSG.oddCore Y).map e.symm.toMonoidHom ≤ CFSG.oddCore X :=
      le_sSup ⟨(CFSG.oddCore_normal Y).map _ e.symm.surjective,
        by rw [Subgroup.card_map_of_injective e.symm.injective]; exact odd_card_oddCore Y⟩
    intro y hy
    exact ⟨e.symm y, hle ⟨y, hy, rfl⟩, by simp⟩

noncomputable def conjSubEquiv (g : G) (H : Subgroup G) : H ≃* conjSub g H :=
  H.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

theorem subtype_comp_conjSubEquiv (g : G) (H : Subgroup G) :
    (conjSub g H).subtype.comp (conjSubEquiv g H).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp H.subtype := by
  ext x
  rfl

theorem oddCoreIn_conjSub [Finite G] (g : G) (H : Subgroup G) :
    oddCoreIn (conjSub g H) = conjSub g (oddCoreIn H) := by
  rw [oddCoreIn, oddCoreIn, ← oddCore_map_mulEquiv' (conjSubEquiv g H), Subgroup.map_map,
    subtype_comp_conjSubEquiv, conjSub, Subgroup.map_map]

theorem pCoreIn_conjSub (p : ℕ) (g : G) (H : Subgroup G) :
    pCoreIn p (conjSub g H) = conjSub g (pCoreIn p H) := by
  rw [pCoreIn, pCoreIn, ← CFSG.pCore_map_iso p (conjSubEquiv g H), Subgroup.map_map,
    subtype_comp_conjSubEquiv, conjSub, Subgroup.map_map]

theorem le_pCoreIn {p : ℕ} {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hK : IsPGroup p K) : K ≤ pCoreIn p H := by
  have hnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hnorm
  have hp : IsPGroup p (K.subgroupOf H) := hK.comap_subtype
  have hle : K.subgroupOf H ≤ CFSG.pCore p H := le_sSup ⟨hnormal, hp⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

theorem isPGroup_pCoreIn (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreIn p H) :=
  CFSG.pCore_isPGroup.map _

theorem le_normalizer_pCoreIn (p : ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((pCoreIn p H : Subgroup G) : Set G) :=
  le_normalizer_map_subtype H (CFSG.pCore p H)

theorem pCoreIn_le_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {H P : Subgroup G}
    (hP : IsSylowOf p P H) : pCoreIn p H ≤ P := by
  obtain ⟨Q, rfl⟩ := hP
  exact Subgroup.map_mono (CFSG.pCore_isPGroup.le_sylow_of_normal Q)

end Cores

section OddOrder

theorem odd_orderOf_of_mem {K : Subgroup G} (hK : Odd (Nat.card K)) {u : G} (hu : u ∈ K) :
    Odd (orderOf u) :=
  hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hu)

theorem mem_of_sq_mem {u : G} (hu : Odd (orderOf u)) {K : Subgroup G} (h : u ^ 2 ∈ K) :
    u ∈ K := by
  obtain ⟨m, hm⟩ := hu
  have : u = (u ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf u + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [this]
  exact K.pow_mem h _

theorem eq_one_of_sq_eq_one {u : G} (hu : Odd (orderOf u)) (h : u ^ 2 = 1) : u = 1 := by
  have := mem_of_sq_mem hu (K := ⊥) (by rw [h]; exact Subgroup.one_mem _)
  exact Subgroup.mem_bot.mp this

theorem odd_card_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G}
    (hK : IsPGroup p K) : Odd (Nat.card K) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

theorem inf_eq_bot_of_two_odd [Finite G] {T K : Subgroup G} (hT : IsPGroup 2 T)
    (hK : Odd (Nat.card K)) : T ⊓ K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
  apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
  rw [hn]
  exact (Nat.coprime_two_left.mpr hK).pow_left n

theorem mem_centralizer_of_mem_normalizer [Finite G] {T K : Subgroup G} (hT : IsPGroup 2 T)
    (hK : Odd (Nat.card K)) (hTK : T ≤ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K)
    (hkT : k ∈ Subgroup.normalizer (T : Set G)) : k ∈ Subgroup.centralizer (T : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h1 : k * t * k⁻¹ * t⁻¹ ∈ T :=
    T.mul_mem ((Subgroup.mem_normalizer_iff.mp hkT t).mp ht) (T.inv_mem ht)
  have h2 : k * t * k⁻¹ * t⁻¹ ∈ K := by
    have : t * k⁻¹ * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hTK ht) k⁻¹).mp (K.inv_mem hk)
    rw [show k * t * k⁻¹ * t⁻¹ = k * (t * k⁻¹ * t⁻¹) by group]
    exact K.mul_mem hk this
  have h3 : k * t * k⁻¹ * t⁻¹ ∈ T ⊓ K := ⟨h1, h2⟩
  rw [inf_eq_bot_of_two_odd hT hK, Subgroup.mem_bot] at h3
  calc t * k = (k * t * k⁻¹ * t⁻¹)⁻¹ * k * t := by group
    _ = k * t := by rw [h3, inv_one, one_mul]

end OddOrder

section Complement

variable [Finite G]

theorem le_oddCoreIn_of_hasNormalPComplement {X K : Subgroup G}
    (hX : CFSG.HasNormalPComplement 2 X) (hKX : K ≤ X) (hK : Odd (Nat.card K)) :
    K ≤ oddCoreIn X := by
  obtain ⟨N, hN, hcop, h2⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNO : N ≤ CFSG.oddCore X := le_sSup ⟨hN, Nat.coprime_two_left.mp hcop⟩
  set K' : Subgroup X := K.subgroupOf X
  have hK' : Odd (Nat.card K') := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv]
  have himg2 : IsPGroup 2 (K'.map (QuotientGroup.mk' N)) := h2.to_subgroup _
  have himgodd : Odd (Nat.card (K'.map (QuotientGroup.mk' N))) :=
    hK'.of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hbot : K'.map (QuotientGroup.mk' N) = ⊥ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp himg2
    rw [hn] at himgodd
    rcases n with _ | n
    · rw [pow_zero] at hn
      exact Subgroup.card_eq_one.mp hn
    · exact absurd himgodd (by rw [Nat.not_odd_iff_even]; exact (even_two.pow_of_ne_zero
        (Nat.succ_ne_zero n)))
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro k hk
  exact ⟨⟨k, hKX hk⟩, hNO (hbot hk), rfl⟩

theorem exists_relIndex_oddCoreIn_eq_two_pow {X : Subgroup G}
    (hX : CFSG.HasNormalPComplement 2 X) : ∃ k : ℕ, (oddCoreIn X).relIndex X = 2 ^ k := by
  obtain ⟨N, hN, hcop, h2⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNO : N ≤ CFSG.oddCore X := le_sSup ⟨hN, Nat.coprime_two_left.mp hcop⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  have hidx : N.index = 2 ^ n := by rw [Subgroup.index_eq_card, hn]
  have hdvd : (CFSG.oddCore X).index ∣ 2 ^ n := hidx ▸ Subgroup.index_dvd_of_le hNO
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨k, ?_⟩
  rw [oddCoreIn, Subgroup.relIndex, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
  exact hk

end Complement

section CoprimeAction

@[expose, reducible] def conjActOn (T K : Subgroup G) (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    MulDistribMulAction T K where
  smul t k := ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTK t.2) k).mp k.2⟩
  one_smul k := Subtype.ext (by change (1 : G) * k * 1⁻¹ = k; group)
  mul_smul s t k := Subtype.ext (by
    change (s * t : G) * k * (s * t : G)⁻¹ = s * (t * k * (t : G)⁻¹) * (s : G)⁻¹
    group)
  smul_mul t k l := Subtype.ext (by
    change (t : G) * (k * l) * (t : G)⁻¹ = (t * k * (t : G)⁻¹) * (t * l * (t : G)⁻¹)
    group)
  smul_one t := Subtype.ext (by change (t : G) * 1 * (t : G)⁻¹ = 1; group)

variable [Finite G] {T K : Subgroup G}

theorem exists_isSylowOf_le_normalizer (hT : IsPGroup 2 T) (hK : Odd (Nat.card K))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (r : ℕ) [Fact r.Prime] :
    ∃ V : Subgroup G, IsSylowOf r V K ∧ T ≤ Subgroup.normalizer (V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := conjActOn T K hTK
  obtain ⟨P₀⟩ : Nonempty (Sylow r K) := inferInstance
  have hnd : ¬ 2 ∣ Nat.card (Sylow r K) := fun h2 =>
    (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr
      (h2.trans ((Sylow.card_dvd_index P₀).trans (Subgroup.index_dvd_card _))))
  obtain ⟨P, hP⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card (Sylow r K) hnd
  refine ⟨(P : Subgroup K).map K.subtype, ⟨P, rfl⟩, fun t ht => ?_⟩
  have htP : ∀ u : T, ∀ z : K, z ∈ (P : Subgroup K) ↔ u⁻¹ • z ∈ (P : Subgroup K) := by
    intro u z
    have := congrArg (fun Q : Sylow r K => z ∈ (Q : Subgroup K)) (hP u)
    simp only [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
    exact (Iff.of_eq this).symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : (⟨t, ht⟩ : T)⁻¹⁻¹ • z ∈ (P : Subgroup K) := by
      rwa [← htP]
    refine ⟨_, hz', ?_⟩
    simp only [inv_inv]
    rfl
  · rintro ⟨z, hz, hzx⟩
    have hxK : x ∈ K := by
      have : x = t⁻¹ * (z : G) * t := by
        rw [Subgroup.coe_subtype] at hzx
        rw [hzx]
        group
      rw [this]
      exact (Subgroup.mem_normalizer_iff''.mp (hTK ht) z).mp z.2
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    change (⟨x, hxK⟩ : K) ∈ (P : Subgroup K)
    rw [htP ⟨t, ht⟩⁻¹]
    have heq : (⟨t, ht⟩ : T)⁻¹⁻¹ • (⟨x, hxK⟩ : K) = z := by
      apply Subtype.ext
      rw [Subgroup.coe_subtype] at hzx
      change ((⟨t, ht⟩ : T)⁻¹⁻¹ : T) * x * (((⟨t, ht⟩ : T)⁻¹⁻¹ : T) : G)⁻¹ = z
      simp only [inv_inv]
      exact hzx.symm
    rw [heq]
    exact hz

theorem mem_normalizer_of_conj_le {s : G} {V : Subgroup G}
    (h : ∀ v ∈ V, s * v * s⁻¹ ∈ V) : s ∈ Subgroup.normalizer (V : Set G) := by
  have hle : conjSub s V ≤ V := by
    intro x hx
    rw [mem_conjSub] at hx
    have := h _ hx
    rwa [show s * (s⁻¹ * x * s) * s⁻¹ = x by group] at this
  have heq : conjSub s V = V := Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · exact h v
  · intro hv
    rw [← heq, mem_conjSub] at hv
    rwa [show s⁻¹ * (s * v * s⁻¹) * s = v by group] at hv

theorem exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {V S : Subgroup G}
    (hS : IsPGroup p S) (hVS : V ≤ S) (hne : V ≠ S) :
    ∃ s ∈ S, s ∈ Subgroup.normalizer (V : Set G) ∧ s ∉ V := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : V.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm hVS
    intro x hx
    have : (⟨x, hx⟩ : S) ∈ V.subgroupOf S := htop ▸ Subgroup.mem_top _
    exact this
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := S) _ hlt
  obtain ⟨s, hsN, hsV⟩ := IsConcreteLE.exists_of_lt hnorm
  refine ⟨s, s.2, ?_, hsV⟩
  apply mem_normalizer_of_conj_le
  intro v hv
  exact (Subgroup.mem_normalizer_iff.mp hsN ⟨v, hVS hv⟩).mp hv

theorem isSylowOf_of_isSylowOf_inf_normalizer {p : ℕ} [Fact p.Prime] {V : Subgroup G}
    (hVK : V ≤ K) (hV : IsPGroup p V)
    (hsyl : IsSylowOf p V (K ⊓ Subgroup.normalizer (V : Set G))) : IsSylowOf p V K := by
  classical
  have hV' : IsPGroup p (V.subgroupOf K) := hV.comap_subtype
  obtain ⟨Q, hQ⟩ := hV'.exists_le_sylow
  set S : Subgroup G := (Q : Subgroup K).map K.subtype with hSdef
  have hSsyl : IsSylowOf p S K := ⟨Q, rfl⟩
  have hVS : V ≤ S := by
    intro v hv
    exact ⟨⟨v, hVK hv⟩, hQ hv, rfl⟩
  by_cases hVSeq : V = S
  · rw [hVSeq]
    exact hSsyl
  exfalso
  obtain ⟨s, hsS, hsNG, hsV⟩ := exists_mem_normalizer_not_mem hSsyl.isPGroup hVS hVSeq
  have hsK : s ∈ K := hSsyl.le hsS
  have hle : V ⊔ Subgroup.zpowers s ≤ K ⊓ Subgroup.normalizer (V : Set G) := by
    apply sup_le (le_inf hVK Subgroup.le_normalizer)
    rw [Subgroup.zpowers_le]
    exact ⟨hsK, hsNG⟩
  have hp : IsPGroup p (V ⊔ Subgroup.zpowers s : Subgroup G) :=
    hSsyl.isPGroup.to_le (sup_le hVS ((Subgroup.zpowers_le).mpr hsS))
  have heq := hsyl.eq_of_le le_sup_left hle hp
  apply hsV
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem exists_isSylowOf_le_normalizer_of_le (hT : IsPGroup 2 T) (hK : Odd (Nat.card K))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {r : ℕ} [Fact r.Prime] {U : Subgroup G}
    (hUK : U ≤ K) (hU : IsPGroup r U) (hTU : T ≤ Subgroup.normalizer (U : Set G)) :
    ∃ V : Subgroup G, IsSylowOf r V K ∧ U ≤ V ∧ T ≤ Subgroup.normalizer (V : Set G) := by
  classical
  let 𝓐 : Set (Subgroup G) :=
    {V | U ≤ V ∧ V ≤ K ∧ IsPGroup r V ∧ T ≤ Subgroup.normalizer (V : Set G)}
  obtain ⟨V, hVmax⟩ := 𝓐.toFinite.exists_maximal ⟨U, le_rfl, hUK, hU, hTU⟩
  obtain ⟨hUV, hVK, hVp, hTV⟩ := hVmax.prop
  refine ⟨V, ?_, hUV, hTV⟩
  set N : Subgroup G := K ⊓ Subgroup.normalizer (V : Set G) with hNdef
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := fun t ht =>
    mem_normalizer_inf (hTK ht) (mem_normalizer_normalizer (hTV ht))
  have hNodd : Odd (Nat.card N) := hK.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨W, hWsyl, hTW⟩ := exists_isSylowOf_le_normalizer hT hNodd hTN r
  have hVN : V ≤ N := le_inf hVK Subgroup.le_normalizer
  have hVW : V ≤ W := by
    obtain ⟨Q, rfl⟩ := hWsyl
    have hnormal : (V.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVN).mpr inf_le_right
    have hle := @IsPGroup.le_sylow_of_normal _ _ _ _ hnormal (hVp.comap_subtype (K := N)) Q
    intro v hv
    exact ⟨⟨v, hVN hv⟩, hle hv, rfl⟩
  have hWmem : W ∈ 𝓐 := ⟨hUV.trans hVW, hWsyl.le.trans inf_le_left, hWsyl.isPGroup, hTW⟩
  have hWV : W = V := le_antisymm (hVmax.2 hWmem hVW) hVW
  apply isSylowOf_of_isSylowOf_inf_normalizer hVK hVp
  rw [hWV] at hWsyl
  exact hWsyl

theorem exists_conj_of_isSylowOf_le_normalizer (hT : IsPGroup 2 T) (hK : Odd (Nat.card K))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {r : ℕ} [Fact r.Prime] {V V' : Subgroup G}
    (hV : IsSylowOf r V K) (hV' : IsSylowOf r V' K) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hTV' : T ≤ Subgroup.normalizer (V' : Set G)) :
    ∃ c ∈ K ⊓ Subgroup.centralizer (T : Set G), conjSub c V = V' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := conjActOn T K hTK
  obtain ⟨Q, rfl⟩ := hV
  obtain ⟨Q', rfl⟩ := hV'
  have hinv : ∀ {P : Sylow r K}, T ≤ Subgroup.normalizer
      (((P : Subgroup K).map K.subtype : Subgroup G) : Set G) →
      ∀ a : T, ∀ x ∈ (P : Subgroup K), a • x ∈ (P : Subgroup K) := by
    intro P hTP a x hx
    have hmem : (a : G) * x * (a : G)⁻¹ ∈ (P : Subgroup K).map K.subtype :=
      (Subgroup.mem_normalizer_iff.mp (hTP a.2) x).mp ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hmem
    have : a • x = y := Subtype.ext hyx.symm
    rw [this]
    exact hy
  have hcard : ¬ 2 ∣ Nat.card K := fun h2 =>
    (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr h2)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  obtain ⟨c, hcfix, hc⟩ := CFSG.SolvableHall.coprime_fixed_conjugator (A := T) (H := K) hT hcard
    (hinv hTV) (hinv hTV') ⟨g⁻¹, by rw [inv_inv, CFSG.SolvableHall.map_conj_eq_coe_smul, hg]⟩
  refine ⟨((c⁻¹ : K) : G), Subgroup.mem_inf.mpr ⟨(c⁻¹).2, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hfix := (FixedPoints.mem_subgroup T K c).mp hcfix ⟨t, ht⟩
    have hval : t * (c : G) * t⁻¹ = c := congrArg Subtype.val hfix
    calc t * ((c⁻¹ : K) : G) = (t * (c : G) * t⁻¹)⁻¹ * t := by simp [mul_assoc]
      _ = ((c⁻¹ : K) : G) * t := by rw [hval]; simp
  · rw [← hc, conjSub, Subgroup.map_map, Subgroup.map_map]
    congr 1

end CoprimeAction

section Core

theorem le_pCoreIn_sup_of_le {p : ℕ} {U C Y : Subgroup G} (hUC : (U : Set G) * C = C * U)
    (hU : IsPGroup p U) (hYU : Y ≤ U) (hCY : C ≤ Subgroup.normalizer (Y : Set G)) :
    Y ≤ pCoreIn p (U ⊔ C) := by
  set X : Subgroup G := U ⊔ C with hX
  set N : Subgroup X := (U.subgroupOf X).normalCore with hN
  have hNp : IsPGroup p N :=
    (hU.comap_subtype (K := X)).to_le (Subgroup.normalCore_le _)
  have hNle : N ≤ CFSG.pCore p X := le_sSup ⟨Subgroup.normalCore_normal _, hNp⟩
  have hYN : Y.subgroupOf X ≤ N := by
    intro y hy b
    obtain ⟨u, hu, c, hc, hb⟩ := mem_sup_of_mul_comm hUC b.2
    rw [Subgroup.mem_subgroupOf]
    have hy' : (y : G) ∈ Y := hy
    have hcy : c * y * c⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hCY hc) y).mp hy'
    change (b : G) * y * (b : G)⁻¹ ∈ U
    rw [← hb, show u * c * (y : G) * (u * c)⁻¹ = u * (c * y * c⁻¹) * u⁻¹ by group]
    exact U.mul_mem (U.mul_mem hu (hYU hcy)) (U.inv_mem hu)
  intro y hy
  have hyX : y ∈ X := (le_sup_left : U ≤ X) (hYU hy)
  exact ⟨⟨y, hyX⟩, hNle (hYN hy), rfl⟩

end Core

end CFSG.ABGTheoremB.TotallyInverted.Omnibus
