module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.Core
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.EOffender

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.Quasithin.A4
  CFSG.QuasithinUnique
open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
open CFSG.HardMathSupport.RichardWeiss.Proving
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_conj_mem' {H : Subgroup G} {g : G}
    (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem le_of_normal_of_swap_mem {α : Type*} [Fintype α] [DecidableEq α] {M L K : Subgroup G}
    (θ : ↥M →* Perm α) (hLM : L ≤ M) (hperf : ⁅L, L⁆ = L)
    (hker : ∀ m : ↥M, θ m = 1 → ∃ n : ℕ, m ^ 2 ^ n = 1)
    (hAlt : ∀ σ ∈ alternatingGroup α, ∃ m : ↥M, θ m = σ)
    (hKn : M ≤ Subgroup.normalizer (K : Set G))
    (t : ↥M) (ht : (θ t).IsSwap) (htK : (t : G) ∈ K) : L ≤ K := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : Function.Surjective θ := by
    intro σ
    by_cases hs : sign σ = 1
    · obtain ⟨m, hm⟩ := hAlt σ (mem_alternatingGroup.2 hs)
      exact ⟨m, hm⟩
    · have hs' : sign σ = -1 := by
        rcases Int.units_eq_one_or (sign σ) with h | h
        · exact absurd h hs
        · exact h
      have h1 : sign (σ * θ t) = 1 := by
        rw [Perm.sign_mul, hs', ht.sign_eq]; decide
      obtain ⟨m, hm⟩ := hAlt _ (mem_alternatingGroup.2 h1)
      refine ⟨m * t⁻¹, ?_⟩
      rw [map_mul, map_inv, hm, mul_inv_cancel_right]
  set K' : Subgroup ↥M := K.subgroupOf M with hK'
  have hK'n : K'.Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [hK', Subgroup.mem_subgroupOf] at hk ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hKn g.2) k).1 hk
    simpa using this
  have hθKn : (K'.map θ).Normal := hK'n.map θ hsurj
  have htK' : θ t ∈ K'.map θ :=
    Subgroup.mem_map.2 ⟨t, by rw [hK', Subgroup.mem_subgroupOf]; exact htK, rfl⟩
  have hswaps : ∀ σ : Perm α, σ.IsSwap → σ ∈ K'.map θ := by
    intro σ hσ
    obtain ⟨a, b, hab, hθt⟩ := ht
    obtain ⟨x, y, hxy, rfl⟩ := hσ
    obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_swap hab hxy)
    rw [← hc]
    exact hθKn.conj_mem _ (hθt ▸ htK') c
  have htop : K'.map θ = ⊤ := by
    rw [eq_top_iff, ← closure_isSwap, Subgroup.closure_le]
    exact hswaps
  have hp : IsPGroup 2 (↥M ⧸ K') := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have hm : θ m ∈ K'.map θ := htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkm⟩ := Subgroup.mem_map.1 hm
    obtain ⟨n, hn⟩ := hker (k⁻¹ * m) (by rw [map_mul, map_inv, hkm, inv_mul_cancel])
    refine ⟨n, ?_⟩
    have heq : (m : ↥M ⧸ K') = ((k⁻¹ * m : ↥M) : ↥M ⧸ K') := by
      rw [QuotientGroup.eq]
      have hk' : m⁻¹ * k⁻¹ * m ∈ K' := by
        have := hK'n.conj_mem _ (K'.inv_mem hk) m⁻¹
        simpa [mul_assoc] using this
      have e : m⁻¹ * (k⁻¹ * m) = m⁻¹ * k⁻¹ * m := by group
      rw [e]
      exact hk'
    rw [heq, ← QuotientGroup.mk_pow, hn, QuotientGroup.mk_one]
  let f : ↥L →* ↥M ⧸ K' := (QuotientGroup.mk' K').comp (Subgroup.inclusion hLM)
  have hLperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have hr : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hrp : IsPGroup 2 f.range := hp.to_subgroup _
  have hnil : Group.IsNilpotent f.range := hrp.isNilpotent
  have hsub : Subsingleton f.range := by
    by_contra hn
    have : Nontrivial f.range := not_subsingleton_iff_nontrivial.mp hn
    exact Group.IsPerfect.not_isNilpotent f.range hnil
  intro x hx
  have h1 : f ⟨x, hx⟩ = 1 := by
    have := Subsingleton.elim (⟨f ⟨x, hx⟩, ⟨_, rfl⟩⟩ : f.range) 1
    exact congrArg Subtype.val this
  have h2 : (⟨x, hLM hx⟩ : ↥M) ∈ K' := (QuotientGroup.eq_one_iff _).1 h1
  rw [hK', Subgroup.mem_subgroupOf] at h2
  exact h2

omit [Finite G] in
theorem le_normalizer_cenS {S L : Subgroup G} {α : Type*} (θ : ↥(L ⊔ S) →* Perm α)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hcen : ∀ m : ↥(L ⊔ S), (m : G) ∈ Subgroup.centralizer (blockV S L : Set G) → θ m = 1) :
    L ⊔ S ≤ Subgroup.normalizer (cenS S (blockV S L) : Set G) := by
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L
  have key : ∀ g ∈ L ⊔ S, ∀ x ∈ cenS S (blockV S L), g * x * g⁻¹ ∈ cenS S (blockV S L) := by
    intro g hg x hx
    have hx' : x ∈ Subgroup.centralizer (blockV S L : Set G) ⊓ S := hx
    obtain ⟨hxC, hxS⟩ := Subgroup.mem_inf.1 hx'
    have hxM : x ∈ L ⊔ S := (le_sup_right : S ≤ L ⊔ S) hxS
    have hC : g * x * g⁻¹ ∈ Subgroup.centralizer (blockV S L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : g⁻¹ * v * g ∈ blockV S L := by
        have := (Subgroup.mem_normalizer_iff.1 (hMV (inv_mem hg)) v).1 hv
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.1 hxC _ hv'
      calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
        _ = g * x * g⁻¹ * v := by group
    have hgx : g * x * g⁻¹ ∈ L ⊔ S := mul_mem (mul_mem hg hxM) (inv_mem hg)
    show g * x * g⁻¹ ∈ Subgroup.centralizer (blockV S L : Set G) ⊓ S
    exact Subgroup.mem_inf.2 ⟨hC, hθS ⟨_, hgx⟩ (hcen ⟨_, hgx⟩ hC)⟩
  intro g hg
  exact mem_normalizer_of_conj_mem' (key g hg) fun x hx => by
    simpa using key g⁻¹ (inv_mem hg) x hx

omit [Finite G] in
theorem exists_pow_eq_one_of_ker {S M : Subgroup G} {α : Type*} (hS2 : IsPGroup 2 S)
    (θ : ↥M →* Perm α) (hθS : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S) :
    ∀ m : ↥M, θ m = 1 → ∃ n : ℕ, m ^ 2 ^ n = 1 := by
  intro m hm
  obtain ⟨n, hn⟩ := hS2 ⟨m, hθS m hm⟩
  exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩

theorem commutator_mem_blockV_of_mem_omegaOneCenter {S L : Subgroup G}
    (hS2 : IsPGroup 2 S) (hperf : ⁅L, L⁆ = L) {α : Type*} [Fintype α] [DecidableEq α]
    (θ : ↥(L ⊔ S) →* Perm α)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hcen : ∀ m : ↥(L ⊔ S), (m : G) ∈ Subgroup.centralizer (blockV S L : Set G) → θ m = 1)
    (hAlt : ∀ σ ∈ alternatingGroup α, ∃ m : ↥(L ⊔ S), θ m = σ)
    (hD : EOffenderData S (blockV S L))
    (t : ↥(L ⊔ S)) (ht : (θ t).IsSwap) (htJ : (t : G) ∈ thompsonJ S) :
    ∀ z ∈ omegaOneCenterOf (thompsonJ S), ∀ l ∈ L, l * z * l⁻¹ * z⁻¹ ∈ blockV S L := by
  set V := blockV S L with hV
  set E := eOf S V with hE
  have hMV : L ⊔ S ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L
  have hME : L ⊔ S ≤ Subgroup.normalizer (E : Set G) := fun m hm =>
    normalizer_le_normalizer_eOf S _ (le_normalizer_cenS θ hθS hcen hm)
  have hVn : ∀ m ∈ L ⊔ S, ∀ v ∈ V, m * v * m⁻¹ ∈ V := fun m hm v hv =>
    (Subgroup.mem_normalizer_iff.1 (hMV hm) v).1 hv
  have hEn : ∀ m ∈ L ⊔ S, ∀ x ∈ E, m * x * m⁻¹ ∈ E := fun m hm x hx =>
    (Subgroup.mem_normalizer_iff.1 (hME hm) x).1 hx
  let K₁ : Subgroup G :=
    { carrier := {m | m ∈ L ⊔ S ∧ ∀ x ∈ E, m * x * m⁻¹ * x⁻¹ ∈ V}
      one_mem' := ⟨(L ⊔ S).one_mem, fun x _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(L ⊔ S).mul_mem ha hb, fun x hx => ?_⟩
        have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
            a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
        rw [e]
        exact V.mul_mem (hVn a ha _ (hb' x hx)) (ha' x hx)
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(L ⊔ S).inv_mem ha, fun x hx => ?_⟩
        have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact hVn _ ((L ⊔ S).inv_mem ha) _ (V.inv_mem (ha' x hx)) }
  have hK₁n : L ⊔ S ≤ Subgroup.normalizer (K₁ : Set G) := by
    have key : ∀ g ∈ L ⊔ S, ∀ m ∈ K₁, g * m * g⁻¹ ∈ K₁ := by
      rintro g hg m ⟨hm, hm'⟩
      refine ⟨mul_mem (mul_mem hg hm) (inv_mem hg), fun x hx => ?_⟩
      have hx' : g⁻¹ * x * g ∈ E := by simpa using hEn _ (inv_mem hg) x hx
      have e : g * m * g⁻¹ * x * (g * m * g⁻¹)⁻¹ * x⁻¹ =
          g * (m * (g⁻¹ * x * g) * m⁻¹ * (g⁻¹ * x * g)⁻¹) * g⁻¹ := by group
      rw [e]
      exact hVn g hg _ (hm' _ hx')
    intro g hg
    exact mem_normalizer_of_conj_mem' (key g hg) fun m hm => by
      simpa using key g⁻¹ (inv_mem hg) m hm
  have htK : (t : G) ∈ K₁ := by
    refine ⟨t.2, fun x hx => ?_⟩
    have h1 : ⁅x, (t : G)⁆ ∈ ⁅E, thompsonJ S⁆ := Subgroup.commutator_mem_commutator hx htJ
    have h2 := V.inv_mem (hD.commutator_le h1)
    have e : (t : G) * x * (t : G)⁻¹ * x⁻¹ = ⁅x, (t : G)⁆⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact h2
  have hLK := le_of_normal_of_swap_mem θ (le_sup_left : L ≤ L ⊔ S) hperf
    (exists_pow_eq_one_of_ker hS2 θ hθS) hAlt hK₁n t ht htK
  intro z hz l hl
  exact (hLK hl).2 z (hD.omegaOneCenter_le_eOf hz)

theorem commute_commutator_of_mem_omegaOneCenter {S L : Subgroup G}
    (hS2 : IsPGroup 2 S) (hperf : ⁅L, L⁆ = L) {α : Type*} [Fintype α] [DecidableEq α]
    (θ : ↥(L ⊔ S) →* Perm α)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hcen : ∀ m : ↥(L ⊔ S), (m : G) ∈ Subgroup.centralizer (blockV S L : Set G) → θ m = 1)
    (hAlt : ∀ σ ∈ alternatingGroup α, ∃ m : ↥(L ⊔ S), θ m = σ)
    (hD : EOffenderData S (blockV S L))
    (t : ↥(L ⊔ S)) (ht : (θ t).IsSwap) (htJ : (t : G) ∈ thompsonJ S) :
    ∀ z ∈ omegaOneCenterOf (thompsonJ S), ∀ k : ↥(L ⊔ S), θ k = 1 → ∀ l ∈ L,
      l * ⁅(k : G), z⁆ = ⁅(k : G), z⁆ * l := by
  set V := blockV S L with hV
  set Q := cenS S V with hQ
  set Z₀ := omegaOneCenterOf (thompsonJ S) with hZ₀
  set X₁ : Subgroup G := ⁅Q, Z₀⁆ with hX₁
  have hZL := commutator_mem_blockV_of_mem_omegaOneCenter hS2 hperf θ hθS hcen hAlt hD t ht htJ
  have hMQ : L ⊔ S ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_cenS θ hθS hcen
  have hSZ : S ≤ Subgroup.normalizer (Z₀ : Set G) := fun s hs =>
    CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf _
      (ExceptionalClosure.mem_normalizer_thompsonJ_of_mem_normalizer (Subgroup.le_normalizer hs))
  have hQS : Q ≤ S := inf_le_right
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := inf_le_left
  have hX₁Z : X₁ ≤ Z₀ := Subgroup.le_normalizer_iff_commutator_le_right.1 (hQS.trans hSZ)
  have hZQ : Z₀ ≤ Q := hD.omegaOneCenter_le_eOf.trans (eOf_le_cenS S V)
  have hLX : ∀ l ∈ L, ∀ x ∈ X₁, l * x * l⁻¹ ∈ X₁ := by
    intro l hl x hx
    have hlM : l ∈ L ⊔ S := (le_sup_left : L ≤ L ⊔ S) hl
    rw [hX₁, Subgroup.commutator_def] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, hk, z, hz, rfl⟩ := hy
      apply Subgroup.subset_closure
      set k' := l * k * l⁻¹ with hk'
      set u := l * z * l⁻¹ * z⁻¹ with hu
      have hk'Q : k' ∈ Q := (Subgroup.mem_normalizer_iff.1 (hMQ hlM) k).1 hk
      have huV : u ∈ V := hZL z hz l hl
      have hku : k' * u = u * k' := (Subgroup.mem_centralizer_iff.1 (hQV hk'Q) u huV).symm
      have hcQ : k' * z * k'⁻¹ * z⁻¹ ∈ Q :=
        Q.mul_mem (Q.mul_mem (Q.mul_mem hk'Q (hZQ hz)) (Q.inv_mem hk'Q)) (Q.inv_mem (hZQ hz))
      have hcu : (k' * z * k'⁻¹ * z⁻¹) * u = u * (k' * z * k'⁻¹ * z⁻¹) :=
        (Subgroup.mem_centralizer_iff.1 (hQV hcQ) u huV).symm
      refine ⟨k', hk'Q, z, hz, ?_⟩
      have e1 : l * ⁅k, z⁆ * l⁻¹ = k' * (u * z) * k'⁻¹ * (u * z)⁻¹ := by
        rw [hk', hu, commutatorElement_def]; group
      have e2 : k' * (u * z) * k'⁻¹ * (u * z)⁻¹ =
          u * (k' * z * k'⁻¹ * z⁻¹) * u⁻¹ := by
        rw [← mul_assoc k' u z, hku]; group
      rw [e1, e2, ← hcu, mul_inv_cancel_right, commutatorElement_def]
    | one => simp
    | mul y z _ _ hy hz =>
      have : l * (y * z) * l⁻¹ = (l * y * l⁻¹) * (l * z * l⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ hy hz
    | inv y _ hy =>
      have : l * y⁻¹ * l⁻¹ = (l * y * l⁻¹)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ hy
  have hLN : L ≤ Subgroup.normalizer (X₁ : Set G) := fun l hl =>
    mem_normalizer_of_conj_mem' (hLX l hl) fun x hx => by
      simpa using hLX l⁻¹ (inv_mem hl) x hx
  have hSN : S ≤ Subgroup.normalizer (X₁ : Set G) := fun s hs =>
    mem_normalizer_of_conj_mem' (fun x hx => conj_mem_commutator' (hMQ
      ((le_sup_right : S ≤ L ⊔ S) hs)) (hSZ hs) hx) fun x hx => by
      simpa using conj_mem_commutator' (hMQ ((le_sup_right : S ≤ L ⊔ S) (inv_mem hs)))
        (hSZ (inv_mem hs)) hx
  have hMX : L ⊔ S ≤ Subgroup.normalizer (X₁ : Set G) := sup_le hLN hSN
  set K₂ : Subgroup G := (L ⊔ S) ⊓ Subgroup.centralizer (X₁ : Set G) with hK₂
  have hK₂n : L ⊔ S ≤ Subgroup.normalizer (K₂ : Set G) := by
    have key : ∀ g ∈ L ⊔ S, ∀ c ∈ K₂, g * c * g⁻¹ ∈ K₂ := by
      intro g hg c hc
      obtain ⟨hcM, hcX⟩ := Subgroup.mem_inf.1 hc
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hg hcM) (inv_mem hg), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : g⁻¹ * x * g ∈ X₁ := by
        simpa using (Subgroup.mem_normalizer_iff.1 (hMX (inv_mem hg)) x).1 hx
      have h1 := Subgroup.mem_centralizer_iff.1 hcX _ hx'
      calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * x := by group
    intro g hg
    exact mem_normalizer_of_conj_mem' (key g hg) fun c hc => by
      simpa using key g⁻¹ (inv_mem hg) c hc
  have htK : (t : G) ∈ K₂ := by
    refine Subgroup.mem_inf.2 ⟨t.2, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    have hxZ := hX₁Z hx
    have hxZ' : x ∈ centerOf (thompsonJ S) := omegaOneCenterOf_le_centerOf _ hxZ
    have hxC : x ∈ Subgroup.centralizer (thompsonJ S : Set G) := hxZ'.2
    exact (Subgroup.mem_centralizer_iff.1 hxC _ htJ).symm
  have hLK := le_of_normal_of_swap_mem θ (le_sup_left : L ≤ L ⊔ S) hperf
    (exists_pow_eq_one_of_ker hS2 θ hθS) hAlt hK₂n t ht htK
  intro z hz k hk l hl
  have hkQ : (k : G) ∈ Q := Subgroup.mem_inf.2 ⟨hθV k hk, hθS k hk⟩
  have hX : ⁅(k : G), z⁆ ∈ X₁ := Subgroup.commutator_mem_commutator hkQ hz
  exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hLK hl)).2 _ hX).symm

end CFSG.HardMathSupport.RichardWeiss.Coordinator
