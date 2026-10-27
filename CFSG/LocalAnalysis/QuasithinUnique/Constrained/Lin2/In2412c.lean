module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2414b

public section

namespace CFSG.QuasithinUnique.Lin2

section Layers

variable {G : Type*} [Group G]

theorem transitive_lift {R N : Subgroup G} {f : G} (hNR : N ≤ R)
    (hN : ∀ n ∈ N, (f * n) * (f * n) = 1 → ∃ m ∈ N, m⁻¹ * f * m = f * n)
    (hQ : ∀ r ∈ R, ((f * r) * (f * r)) ∈ N → ∃ s ∈ R, ∃ n ∈ N, s⁻¹ * (f * r) * s = f * n)
    {r : G} (hr : r ∈ R) (hr2 : (f * r) * (f * r) = 1) :
    ∃ s ∈ R, s⁻¹ * f * s = f * r := by
  obtain ⟨s, hs, n, hn, e⟩ := hQ r hr (by rw [hr2]; exact N.one_mem)
  have hn2 : (f * n) * (f * n) = 1 := by
    rw [← e]
    calc s⁻¹ * (f * r) * s * (s⁻¹ * (f * r) * s) = s⁻¹ * ((f * r) * (f * r)) * s := by group
      _ = 1 := by rw [hr2]; group
  obtain ⟨m, hm, hmf⟩ := hN n hn hn2
  refine ⟨m * s⁻¹, R.mul_mem (hNR hm) (R.inv_mem hs), ?_⟩
  have e2 : f * r = s * (f * n) * s⁻¹ := by
    calc f * r = s * (s⁻¹ * (f * r) * s) * s⁻¹ := by group
      _ = s * (f * n) * s⁻¹ := by rw [e]
  rw [e2, ← hmf]
  group

theorem layer_hQ {K : Type*} [Field K] (σ : K ≃+* K) (c : K) (hK2 : (2 : K) = 0)
    (hfree : ∀ v : K, c * σ v = v → ∃ w : K, v = c * σ w + w)
    {P P' : Subgroup G} {f : G} (hff : f * f = 1)
    (hfP : ∀ x ∈ P, f * x * f⁻¹ ∈ P)
    (γ : P →* Multiplicative K) (hγsurj : Function.Surjective γ)
    (hγker : ∀ x : P, γ x = 1 ↔ (x : G) ∈ P')
    (hγf : ∀ x : P, Multiplicative.toAdd (γ ⟨f * x * f⁻¹, hfP x x.2⟩) =
      c * σ (Multiplicative.toAdd (γ x))) :
    ∀ r ∈ P, ((f * r) * (f * r)) ∈ P' → ∃ s ∈ P, ∃ n ∈ P', s⁻¹ * (f * r) * s = f * n := by
  have hti : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hneg : ∀ a : K, -a = a := by
    intro a
    have : a + a = 0 := by
      have : a + a = 2 * a := by ring
      rw [this, hK2, zero_mul]
    exact neg_eq_of_add_eq_zero_right this
  intro r hr hr2
  set v := Multiplicative.toAdd (γ ⟨r, hr⟩) with hv
  have hfr : (f * r) * (f * r) = (f * r * f⁻¹) * r := by
    rw [hti]; group
  have h1 : γ ⟨(f * r * f⁻¹) * r, P.mul_mem (hfP r hr) hr⟩ = 1 := by
    rw [hγker]
    show (f * r * f⁻¹) * r ∈ P'
    rw [← hfr]; exact hr2
  have h2 : c * σ v + v = 0 := by
    have : γ ⟨(f * r * f⁻¹) * r, P.mul_mem (hfP r hr) hr⟩ =
        γ ⟨f * r * f⁻¹, hfP r hr⟩ * γ ⟨r, hr⟩ := by
      rw [← map_mul]; rfl
    rw [this] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    rw [toAdd_mul, toAdd_one, hγf ⟨r, hr⟩] at h3
    exact h3
  have h4 : c * σ v = v := by
    have : c * σ v = -v := eq_neg_of_add_eq_zero_left h2
    rw [this]; exact hneg v
  obtain ⟨w, hw⟩ := hfree v h4
  obtain ⟨⟨s, hs⟩, hsw⟩ := hγsurj (Multiplicative.ofAdd w)
  have hsw' : Multiplicative.toAdd (γ ⟨s, hs⟩) = w := by rw [hsw]; rfl
  have hfsP : f * s * f⁻¹ ∈ P := hfP s hs
  have hn'P : (f * s * f⁻¹)⁻¹ * r * s ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hfsP) hr) hs
  refine ⟨s, hs, (f * s * f⁻¹)⁻¹ * r * s, ?_, ?_⟩
  · rw [← hγker ⟨_, hn'P⟩]
    have : γ ⟨(f * s * f⁻¹)⁻¹ * r * s, hn'P⟩ =
        (γ ⟨f * s * f⁻¹, hfsP⟩)⁻¹ * γ ⟨r, hr⟩ * γ ⟨s, hs⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [this]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_mul, toAdd_inv, toAdd_one, hγf ⟨s, hs⟩, hsw']
    show -(c * σ w) + v + w = 0
    rw [hw]
    linear_combination w * hK2
  · have hfs : f * (f * s * f⁻¹)⁻¹ = s⁻¹ * f := by
      calc f * (f * s * f⁻¹)⁻¹ = (f * f) * s⁻¹ * f⁻¹ := by group
        _ = s⁻¹ * f⁻¹ := by rw [hff, one_mul]
        _ = s⁻¹ * f := by rw [hti]
    calc s⁻¹ * (f * r) * s = (s⁻¹ * f) * r * s := by group
      _ = (f * (f * s * f⁻¹)⁻¹) * r * s := by rw [hfs]
      _ = f * ((f * s * f⁻¹)⁻¹ * r * s) := by group

theorem layer_card [Finite G] {K : Type*} [Field K] [Finite K] (σ : K ≃+* K) (c : K)
    {P P' : Subgroup G} (hP'P : P' ≤ P) {f : G} (hff : f * f = 1)
    (hfP : ∀ x ∈ P, f * x * f⁻¹ ∈ P) (hfP' : ∀ x ∈ P', f * x * f⁻¹ ∈ P')
    (γ : P →* Multiplicative K) (hγsurj : Function.Surjective γ)
    (hγker : ∀ x : P, γ x = 1 ↔ (x : G) ∈ P')
    (hγf : ∀ x : P, Multiplicative.toAdd (γ ⟨f * x * f⁻¹, hfP x x.2⟩) =
      c * σ (Multiplicative.toAdd (γ x)))
    (hP'ab : ∀ a ∈ P', ∀ b ∈ P', a * b = b * a) (hP'sq : ∀ a ∈ P', a * a = 1)
    (hTr : ∀ x ∈ P', (f * x) * (f * x) = 1 → ∃ m ∈ P', m⁻¹ * f * m = f * x) :
    Nat.card (P ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) =
      Nat.card (P' ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) *
        Nat.card {v : K // c * σ v = v} := by
  have hti : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hff2 : ∀ g : G, f * (f * g * f⁻¹) * f⁻¹ = g := by
    intro g
    calc f * (f * g * f⁻¹) * f⁻¹ = (f * f) * g * (f * f)⁻¹ := by group
      _ = g := by rw [hff]; group
  have hc : ∀ g : G, f⁻¹ * g * f = f * g * f⁻¹ := fun g => by rw [hti]
  set C : Subgroup G := P ⊓ Subgroup.centralizer ({f} : Set G) with hC
  have hCP : C ≤ P := inf_le_left
  let δ : C →* Multiplicative K := γ.comp (Subgroup.inclusion hCP)
  have hδ : ∀ x : C, δ x = γ ⟨x, hCP x.2⟩ := fun _ => rfl
  have hCf : ∀ x : C, f * (x : G) * f⁻¹ = x := by
    intro x
    have := Subgroup.mem_centralizer_singleton_iff.1 x.2.2
    rw [← this]; group
  have hfix : ∀ x : C, c * σ (Multiplicative.toAdd (δ x)) = Multiplicative.toAdd (δ x) := by
    intro x
    have h1 : γ ⟨f * (x : G) * f⁻¹, hfP x (hCP x.2)⟩ = δ x :=
      congrArg γ (Subtype.ext (hCf x))
    have := hγf ⟨x, hCP x.2⟩
    rw [h1] at this
    exact this.symm
  have hlift : ∀ v : K, c * σ v = v → ∃ x : C, Multiplicative.toAdd (δ x) = v := by
    intro v hv
    obtain ⟨x, hx⟩ := hγsurj (Multiplicative.ofAdd v)
    have hx' : Multiplicative.toAdd (γ x) = v := by rw [hx]; rfl
    set n₁ := (x : G)⁻¹ * (f * (x : G) * f⁻¹) with hn₁
    have hn₁P : n₁ ∈ P := P.mul_mem (P.inv_mem x.2) (hfP x x.2)
    have hn₁P' : n₁ ∈ P' := by
      rw [← hγker ⟨n₁, hn₁P⟩]
      have : γ ⟨n₁, hn₁P⟩ = (γ x)⁻¹ * γ ⟨f * x * f⁻¹, hfP x x.2⟩ := by
        rw [← map_inv, ← map_mul]; rfl
      rw [this]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, toAdd_one, hγf x, hx']
      rw [hv]; ring
    have hfn₁ : f * n₁ * f⁻¹ = n₁⁻¹ := by
      calc f * n₁ * f⁻¹ = (f * (x : G)⁻¹ * f⁻¹) * (f * (f * x * f⁻¹) * f⁻¹) := by
            rw [hn₁]; group
        _ = (f * (x : G)⁻¹ * f⁻¹) * x := by rw [hff2]
        _ = n₁⁻¹ := by rw [hn₁]; group
    have hn₁inv : n₁⁻¹ = n₁ := (eq_inv_of_mul_eq_one_left (hP'sq n₁ hn₁P')).symm
    have hn₁2 : (f * n₁) * (f * n₁) = 1 := by
      calc (f * n₁) * (f * n₁) = (f * n₁ * f⁻¹) * n₁ := by rw [hti]; group
        _ = n₁ * n₁ := by rw [hfn₁, hn₁inv]
        _ = 1 := hP'sq n₁ hn₁P'
    obtain ⟨m, hm, hmf⟩ := hTr n₁ hn₁P' hn₁2
    have hfmP' : f * m * f⁻¹ ∈ P' := hfP' m hm
    have hn₁eq : n₁ = (f * m * f⁻¹)⁻¹ * m := by
      calc n₁ = f⁻¹ * (f * n₁) := by group
        _ = f⁻¹ * (m⁻¹ * f * m) := by rw [hmf]
        _ = (f⁻¹ * m * f)⁻¹ * m := by group
        _ = (f * m * f⁻¹)⁻¹ * m := by rw [hc]
    have hcomm : m * (f * m * f⁻¹) = (f * m * f⁻¹) * m := hP'ab m hm _ hfmP'
    have hfxm : f * ((x : G) * m) * f⁻¹ = (x : G) * m := by
      calc f * ((x : G) * m) * f⁻¹ = (f * x * f⁻¹) * (f * m * f⁻¹) := by group
        _ = ((x : G) * n₁) * (f * m * f⁻¹) := by rw [hn₁]; group
        _ = (x : G) * (((f * m * f⁻¹)⁻¹ * m) * (f * m * f⁻¹)) := by rw [hn₁eq]; group
        _ = (x : G) * m := by
            congr 1
            calc ((f * m * f⁻¹)⁻¹ * m) * (f * m * f⁻¹) =
                  (f * m * f⁻¹)⁻¹ * (m * (f * m * f⁻¹)) := by group
              _ = (f * m * f⁻¹)⁻¹ * ((f * m * f⁻¹) * m) := by rw [hcomm]
              _ = m := by group
    have hxmP : (x : G) * m ∈ P := P.mul_mem x.2 (hP'P hm)
    have hxmC : (x : G) * m ∈ C := by
      refine ⟨hxmP, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc (x : G) * m * f = (f * ((x : G) * m) * f⁻¹) * f := by rw [hfxm]
        _ = f * ((x : G) * m) := by group
    refine ⟨⟨(x : G) * m, hxmC⟩, ?_⟩
    have hγm : γ ⟨m, hP'P hm⟩ = 1 := (hγker _).2 hm
    rw [hδ]
    have : γ ⟨(x : G) * m, hxmP⟩ = γ x := by
      have : γ ⟨(x : G) * m, hxmP⟩ = γ x * γ ⟨m, hP'P hm⟩ := by rw [← map_mul]; rfl
      rw [this, hγm, mul_one]
    show Multiplicative.toAdd (γ ⟨(x : G) * m, hxmP⟩) = v
    rw [this]; exact hx'
  have hrange : ∀ z : Multiplicative K, z ∈ δ.range ↔
      c * σ (Multiplicative.toAdd z) = Multiplicative.toAdd z := by
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      exact hfix x
    · intro hz
      obtain ⟨x, hx⟩ := hlift _ hz
      exact ⟨x, Multiplicative.toAdd.injective hx⟩
  have hcardR : Nat.card δ.range = Nat.card {v : K // c * σ v = v} :=
    Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd (fun z => hrange z))
  have hkerEq : Nat.card δ.ker =
      Nat.card (P' ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) := by
    let g : δ.ker → (P' ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) := fun x =>
      ⟨((x.1 : C) : G), (hγker ⟨x.1, hCP x.1.2⟩).1 (MonoidHom.mem_ker.1 x.2), x.1.2.2⟩
    have hinj : Function.Injective g := by
      intro x y hxy
      have h1 : ((x.1 : C) : G) = ((y.1 : C) : G) :=
        congrArg (fun z : (P' ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) => (z : G)) hxy
      exact Subtype.ext (Subtype.ext h1)
    have hsurj : Function.Surjective g := by
      rintro ⟨y, hy1, hy2⟩
      refine ⟨⟨⟨y, hP'P hy1, hy2⟩, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker, hδ]
      exact (hγker ⟨y, hP'P hy1⟩).2 hy1
    exact Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)
  have hcard := Subgroup.card_ker_mul_card_of_surjective δ.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict] at hcard
  rw [← hcard, hkerEq, hcardR]

end Layers

section Field

variable {k : Type*} [Field k] [Finite k]

theorem twisted_free (hk2 : (2 : k) = 0) (σ : k ≃+* k) (hσσ : ∀ a, σ (σ a) = a) (θ : k)
    (hθ : σ θ ≠ θ) (c : k) (hc : c * σ c = 1) :
    ∀ v : k, c * σ v = v → ∃ w : k, v = c * σ w + w := by
  have hcount := card_twisted_fixed hk2 σ hσσ θ hθ c hc
  let φ : k →+ k :=
    { toFun := fun a => c * σ a + a
      map_zero' := by simp
      map_add' := by intro a b; simp only [map_add, mul_add]; ring }
  have hneg : ∀ a : k, -a = a := by
    intro a
    have : a + a = 0 := by
      have : a + a = 2 * a := by ring
      rw [this, hk2, zero_mul]
    exact neg_eq_of_add_eq_zero_right this
  have hker : ∀ a, φ a = 0 ↔ c * σ a = a := by
    intro a
    show c * σ a + a = 0 ↔ _
    constructor
    · intro h
      have : c * σ a = -a := eq_neg_of_add_eq_zero_left h
      rw [this]; exact hneg a
    · intro h
      rw [h]
      have : a + a = 2 * a := by ring
      rw [this, hk2, zero_mul]
  have hφφ : ∀ a, φ (φ a) = 0 := by
    intro a
    show c * σ (c * σ a + a) + (c * σ a + a) = 0
    rw [map_add, map_mul, hσσ]
    linear_combination a * hc + (a + c * σ a) * hk2
  have hcardk := AddSubgroup.card_ker_mul_card_of_surjective φ.rangeRestrict_surjective
  rw [AddMonoidHom.ker_rangeRestrict] at hcardk
  have hrange_le : φ.range ≤ φ.ker := by
    rintro _ ⟨a, rfl⟩
    exact (AddMonoidHom.mem_ker).2 (hφφ a)
  have hCker : Nat.card {a : k // c * σ a = a} = Nat.card φ.ker :=
    Nat.card_congr
      (Equiv.subtypeEquivRight (fun a => (hker a).symm.trans AddMonoidHom.mem_ker.symm))
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hrcard : Nat.card φ.range = Nat.card φ.ker := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hcardk, ← hCker, ← sq]
    exact hcount.symm
  have hrange : φ.range = φ.ker :=
    AddSubgroup.eq_of_le_of_card_ge hrange_le (by rw [hrcard])
  intro v hv
  have hv' : v ∈ φ.ker := (AddMonoidHom.mem_ker).2 ((hker v).2 hv)
  rw [← hrange] at hv'
  obtain ⟨w, hw⟩ := hv'
  refine ⟨w, ?_⟩
  have : c * σ w + w = v := hw
  exact this.symm

end Field

section Step

variable {G : Type*} [Group G]

theorem layer_step [Finite G] {K : Type*} [Field K] [Finite K] (σ : K ≃+* K) (c : K)
    (hK2 : (2 : K) = 0) (hσσ : ∀ a, σ (σ a) = a) (θ : K) (hθ : σ θ ≠ θ) (hc : c * σ c = 1)
    {P P' : Subgroup G} (hP'P : P' ≤ P) {f : G} (hff : f * f = 1)
    (hfP : ∀ x ∈ P, f * x * f⁻¹ ∈ P) (hfP' : ∀ x ∈ P', f * x * f⁻¹ ∈ P')
    (γ : P →* Multiplicative K) (hγsurj : Function.Surjective γ)
    (hγker : ∀ x : P, γ x = 1 ↔ (x : G) ∈ P')
    (hγf : ∀ x : P, Multiplicative.toAdd (γ ⟨f * x * f⁻¹, hfP x x.2⟩) =
      c * σ (Multiplicative.toAdd (γ x)))
    (hP'ab : ∀ a ∈ P', ∀ b ∈ P', a * b = b * a) (hP'sq : ∀ a ∈ P', a * a = 1)
    (hTr : ∀ x ∈ P', (f * x) * (f * x) = 1 → ∃ m ∈ P', m⁻¹ * f * m = f * x) :
    (∀ x ∈ P, (f * x) * (f * x) = 1 → ∃ m ∈ P, m⁻¹ * f * m = f * x) ∧
      Nat.card (P ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) =
        Nat.card (P' ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) *
          Nat.card {v : K // c * σ v = v} := by
  have hfree := twisted_free hK2 σ hσσ θ hθ c hc
  refine ⟨fun x hx hx2 => ?_, layer_card σ c hP'P hff hfP hfP' γ hγsurj hγker hγf hP'ab hP'sq hTr⟩
  exact transitive_lift hP'P hTr
    (layer_hQ σ c hK2 hfree hff hfP γ hγsurj hγker hγf) hx hx2


end Step

end CFSG.QuasithinUnique.Lin2
