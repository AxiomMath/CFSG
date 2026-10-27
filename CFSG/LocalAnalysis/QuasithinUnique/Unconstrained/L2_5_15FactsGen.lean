module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Props
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Words

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

section Conj

variable {G : Type} [Group G]

theorem threeCoreCent_conj (g u : G) :
    threeCoreCent (⊤ : Subgroup G) (g * u * g⁻¹) =
      (threeCoreCent (⊤ : Subgroup G) u).map (MulAut.conj g).toMonoidHom := by
  unfold threeCoreCent
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨-, h1, h2⟩
    refine ⟨g⁻¹ * x * g, ⟨Subgroup.mem_top _, ?_, ?_⟩, ?_⟩
    · calc g⁻¹ * x * g * u = g⁻¹ * (x * (g * u * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * u * g⁻¹) * x) * g := by rw [h1]
        _ = u * (g⁻¹ * x * g) := by group
    · have : (MulAut.conj g⁻¹) (x ^ 3) = 1 := by rw [h2, map_one]
      rw [map_pow] at this
      simpa [MulAut.conj_apply] using this
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  · rintro ⟨y, ⟨-, h1, h2⟩, rfl⟩
    refine ⟨Subgroup.mem_top _, ?_, ?_⟩
    · change g * y * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * y * g⁻¹)
      calc g * y * g⁻¹ * (g * u * g⁻¹) = g * (y * u) * g⁻¹ := by group
        _ = g * (u * y) * g⁻¹ := by rw [h1]
        _ = (g * u * g⁻¹) * (g * y * g⁻¹) := by group
    · have : (MulAut.conj g) (y ^ 3) = 1 := by rw [h2, map_one]
      rw [map_pow] at this
      simpa [MulAut.conj_apply] using this

theorem K33InvFacts.conj {u : G} (h : K33InvFacts (⊤ : Subgroup G) u) (g : G) :
    K33InvFacts (⊤ : Subgroup G) (g * u * g⁻¹) where
  mem := by
    rw [threeCoreCent_conj]
    exact ⟨u, h.mem, rfl⟩
  center := by
    intro w hw hcen
    rw [threeCoreCent_conj] at hw hcen
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
    have hc : ∀ v ∈ threeCoreCent (⊤ : Subgroup G) u, v * w₀ = w₀ * v := by
      intro v hv
      have := hcen ((MulAut.conj g).toMonoidHom v) (Subgroup.mem_map_of_mem _ hv)
      have h2 : (MulAut.conj g).toMonoidHom (v * w₀) = (MulAut.conj g).toMonoidHom (w₀ * v) := by
        rw [map_mul, map_mul]; exact this
      exact (MulAut.conj g).injective h2
    rcases h.center w₀ hw₀ hc with rfl | rfl
    · left; exact map_one _
    · right; rfl
  centralizer := by
    intro b hb hcen
    rw [threeCoreCent_conj] at hcen
    have hc : ∀ v ∈ threeCoreCent (⊤ : Subgroup G) u, (g⁻¹ * b * g) * v = v * (g⁻¹ * b * g) := by
      intro v hv
      have := hcen ((MulAut.conj g).toMonoidHom v) (Subgroup.mem_map_of_mem _ hv)
      change b * (g * v * g⁻¹) = g * v * g⁻¹ * b at this
      calc g⁻¹ * b * g * v = g⁻¹ * (b * (g * v * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * v * g⁻¹ * b) * g := by rw [this]
        _ = v * (g⁻¹ * b * g) := by group
    rcases h.centralizer (g⁻¹ * b * g) (Subgroup.mem_top _) hc with h1 | h1
    · left
      have : b = g * (g⁻¹ * b * g) * g⁻¹ := by group
      rw [this, h1]; group
    · right
      have : b = g * (g⁻¹ * b * g) * g⁻¹ := by group
      rw [this, h1]
  aut := by
    intro P hP
    let ι : ↥(threeCoreCent (⊤ : Subgroup G) u) ≃*
        ↥(threeCoreCent (⊤ : Subgroup G) (g * u * g⁻¹)) :=
      ((MulAut.conj g).subgroupMap (threeCoreCent (⊤ : Subgroup G) u)).trans
        (MulEquiv.subgroupCongr (threeCoreCent_conj g u).symm)
    let Φ : MulAut ↥(threeCoreCent (⊤ : Subgroup G) (g * u * g⁻¹)) ≃*
        MulAut ↥(threeCoreCent (⊤ : Subgroup G) u) := MulAut.congr ι.symm
    have hP' : IsPGroup 2 (P.map Φ.toMonoidHom) := hP.map _
    have := h.aut _ hP'
    rwa [Subgroup.card_map_of_injective Φ.injective] at this

end Conj

theorem aut_le_eight {X : Type} [Group X] [Finite X] {u : X} {Tl : List X}
    (hTl : ∀ x : X, (x * u = u * x ∧ x ^ 3 = 1) ↔ x ∈ Tl)
    (a b : X) (ha : a ∈ Tl) (hb : b ∈ Tl)
    (Ws : List (List Bool)) (hgen : ∀ t ∈ Tl, ∃ w ∈ Ws, t = evB a b w)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab2 : (a * b) ^ 2 ≠ 1) (hab4 : (a * b) ^ 4 = 1)
    (Pl : List (X × X))
    (hPl : ∀ x ∈ Tl, ∀ y ∈ Tl, x ≠ 1 → y ≠ 1 → (x * y) ^ 2 ≠ 1 → (x * y) ^ 4 = 1 →
      (x, y) ∈ Pl)
    (hPlc : Pl.length ≤ 24) :
    ∀ P : Subgroup (MulAut ↥(threeCoreCent (⊤ : Subgroup X) u)), IsPGroup 2 P →
      Nat.card P ≤ 8 := by
  classical
  set Q := threeCoreCent (⊤ : Subgroup X) u with hQ
  intro P hP
  have hTmem : ∀ x : X, x ∈ Tl → x ∈ Q := fun x hx =>
    Subgroup.subset_closure ⟨Subgroup.mem_top _, (hTl x).2 hx⟩
  let aQ : Q := ⟨a, hTmem a ha⟩
  let bQ : Q := ⟨b, hTmem b hb⟩
  have hgenQ : ∀ x : Q, x ∈ Subgroup.closure ({aQ, bQ} : Set Q) := by
    rintro ⟨x, hx⟩
    refine Subgroup.closure_induction
      (p := fun x hx => (⟨x, hx⟩ : Q) ∈ Subgroup.closure ({aQ, bQ} : Set Q)) ?_ ?_ ?_ ?_ hx
    · intro x hx'
      obtain ⟨-, hxu, hx3⟩ := hx'
      obtain ⟨w, -, hw⟩ := hgen x ((hTl x).1 ⟨hxu, hx3⟩)
      have hcoe : ((evB aQ bQ w : Q) : X) = evB a b w := by
        simpa using map_evB Q.subtype aQ bQ w
      have : (⟨x, Subgroup.subset_closure ⟨Subgroup.mem_top _, hxu, hx3⟩⟩ : Q) = evB aQ bQ w :=
        Subtype.ext (hw.trans hcoe.symm)
      rw [this]
      exact evB_mem_closure _ _ w
    · exact Subgroup.one_mem _
    · intro x y hx hy hxm hym
      have : (⟨x * y, Subgroup.mul_mem _ hx hy⟩ : Q) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this]
      exact Subgroup.mul_mem _ hxm hym
    · intro x hx hxm
      have : (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : Q) = (⟨x, hx⟩ : Q)⁻¹ := rfl
      rw [this]
      exact Subgroup.inv_mem _ hxm
  have hext : ∀ α β : MulAut Q, α aQ = β aQ → α bQ = β bQ → α = β := by
    intro α β h1 h2
    apply MulEquiv.ext
    intro x
    have hEq : α.toMonoidHom = β.toMonoidHom := by
      apply MonoidHom.ext
      intro y
      exact MonoidHom.eqOn_closure (f := α.toMonoidHom) (g := β.toMonoidHom)
        (s := ({aQ, bQ} : Set Q)) (by
          intro z hz
          rcases hz with rfl | rfl
          · exact h1
          · exact h2) (hgenQ y)
    exact DFunLike.congr_fun hEq x
  let F : MulAut Q → X × X := fun α => ((α aQ : X), (α bQ : X))
  have hF : Function.Injective F := by
    intro α β h
    simp only [F, Prod.mk.injEq] at h
    exact hext α β (Subtype.ext h.1) (Subtype.ext h.2)
  have hFfin : Finite (MulAut Q) := Finite.of_injective F hF
  have hQT : ∀ α : MulAut Q, ∀ z : Q, z ^ 3 = 1 → (α z : X) ∈ Tl := by
    intro α z hz
    refine (hTl _).1 ⟨?_, ?_⟩
    · exact threeCoreCent_comm (α z).2
    · have : (α z) ^ 3 = 1 := by rw [← map_pow, hz, map_one]
      simpa using congrArg Subtype.val this
  have ha3 : aQ ^ 3 = 1 := Subtype.ext ((hTl a).2 ha).2
  have hb3 : bQ ^ 3 = 1 := Subtype.ext ((hTl b).2 hb).2
  have hne : ∀ (α : MulAut Q) (z : Q) (n : ℕ), (z ^ n = 1 ↔ (α z) ^ n = 1) := by
    intro α z n
    rw [← map_pow]
    constructor
    · intro h; rw [h, map_one]
    · intro h; exact α.injective (h.trans (map_one α).symm)
  have hFmem : ∀ α : MulAut Q, F α ∈ Pl := by
    intro α
    refine hPl _ (hQT α aQ ha3) _ (hQT α bQ hb3) ?_ ?_ ?_ ?_
    · intro h
      apply ha1
      have : α aQ = α 1 := by rw [map_one]; exact Subtype.ext h
      exact congrArg Subtype.val (α.injective this)
    · intro h
      apply hb1
      have : α bQ = α 1 := by rw [map_one]; exact Subtype.ext h
      exact congrArg Subtype.val (α.injective this)
    · intro h
      apply hab2
      have h1 : (α aQ * α bQ) ^ 2 = 1 := Subtype.ext (by simpa using h)
      have h2 := (hne α (aQ * bQ) 2).2 (by rw [map_mul]; exact h1)
      simpa using congrArg Subtype.val h2
    · have h1 : (α aQ * α bQ) ^ 4 = 1 := by
        have h2 := (hne α (aQ * bQ) 4).1 (Subtype.ext (by simpa using hab4))
        rwa [map_mul] at h2
      simpa using congrArg Subtype.val h1
  have hcard : Nat.card (MulAut Q) ≤ 24 := by
    have h1 : Nat.card (MulAut Q) ≤ Nat.card ↥Pl.toFinset :=
      Nat.card_le_card_of_injective
        (fun α => (⟨F α, List.mem_toFinset.2 (hFmem α)⟩ : ↥Pl.toFinset))
        (fun α β h => hF (by simpa using congrArg Subtype.val h))
    have h2 : Nat.card ↥Pl.toFinset = Pl.toFinset.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact (h1.trans h2.le).trans ((List.toFinset_card_le Pl).trans hPlc)
  have hnc : ¬ Commute a b := by
    intro hc
    apply hab2
    have h3 : (a * b) ^ 3 = 1 := by
      rw [hc.mul_pow, (hTl a).2 ha |>.2, (hTl b).2 hb |>.2, one_mul]
    have h4 : a * b = 1 := by
      have : (a * b) ^ 4 = (a * b) ^ 3 * (a * b) := pow_succ _ _
      rw [hab4, h3, one_mul] at this
      exact this.symm
    rw [h4]; simp
  have hord : orderOf (MulAut.conj aQ : MulAut Q) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply orderOf_eq_prime
    · rw [← map_pow, ha3, map_one]
    · intro h
      apply hnc
      have := DFunLike.congr_fun h bQ
      have h' : aQ * bQ * aQ⁻¹ = bQ := by simpa [MulAut.conj_apply] using this
      have h'' : aQ * bQ = bQ * aQ := by
        calc aQ * bQ = aQ * bQ * aQ⁻¹ * aQ := by group
          _ = bQ * aQ := by rw [h']
      exact congrArg Subtype.val h''
  have h3N : 3 ∣ Nat.card (MulAut Q) := hord ▸ orderOf_dvd_natCard _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : Nat.card P ∣ Nat.card (MulAut Q) := Subgroup.card_subgroup_dvd_card P
  obtain ⟨m, hm⟩ := h3N
  have hmpos : 0 < m := by
    have := Nat.card_pos (α := MulAut Q)
    omega
  rw [hn, hm] at hdvd
  have h2m : 2 ^ n ∣ m :=
    Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left n (by norm_num)) hdvd
  have := Nat.le_of_dvd hmpos h2m
  rw [hn]
  omega

theorem exists_conj_of_card {X : Type} [Group X] [Finite X] {u₀ : X} {N : ℕ}
    (hcent : Nat.card (Subgroup.centralizer ({u₀} : Set X)) * N = Nat.card X)
    (hN : Nat.card {x : X // x ≠ 1 ∧ x ^ 2 = 1} ≤ N)
    (hu₀1 : u₀ ≠ 1) (hu₀2 : u₀ ^ 2 = 1) :
    ∀ u : X, u ≠ 1 → u ^ 2 = 1 → ∃ g : X, g * u₀ * g⁻¹ = u := by
  classical
  set C := Subgroup.centralizer ({u₀} : Set X) with hC
  let S := {x : X // x ≠ 1 ∧ x ^ 2 = 1}
  have hmem : ∀ g : X, g * u₀ * g⁻¹ ≠ 1 ∧ (g * u₀ * g⁻¹) ^ 2 = 1 := by
    intro g
    refine ⟨?_, ?_⟩
    · intro h
      apply hu₀1
      calc u₀ = g⁻¹ * (g * u₀ * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h]
        _ = 1 := by group
    · have : (MulAut.conj g) (u₀ ^ 2) = 1 := by rw [hu₀2, map_one]
      rw [map_pow] at this
      simpa [MulAut.conj_apply] using this
  have hwd : ∀ g h : X, (g⁻¹ * h ∈ C) → g * u₀ * g⁻¹ = h * u₀ * h⁻¹ := by
    intro g h hgh
    have hc : g⁻¹ * h * u₀ = u₀ * (g⁻¹ * h) := Subgroup.mem_centralizer_singleton_iff.mp hgh
    calc g * u₀ * g⁻¹ = g * (u₀ * (g⁻¹ * h)) * (g⁻¹ * h)⁻¹ * g⁻¹ := by group
      _ = g * ((g⁻¹ * h) * u₀) * (g⁻¹ * h)⁻¹ * g⁻¹ := by rw [← hc]
      _ = h * u₀ * h⁻¹ := by group
  let f : X ⧸ C → S := Quotient.lift (fun g => (⟨g * u₀ * g⁻¹, hmem g⟩ : S)) (by
    intro g h hgh
    apply Subtype.ext
    exact hwd g h (QuotientGroup.leftRel_apply.mp hgh))
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | _ g =>
    induction y using Quotient.inductionOn with
    | _ h =>
    have h1 : g * u₀ * g⁻¹ = h * u₀ * h⁻¹ := congrArg Subtype.val hxy
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * h * u₀ = g⁻¹ * (h * u₀ * h⁻¹) * h := by group
      _ = g⁻¹ * (g * u₀ * g⁻¹) * h := by rw [h1]
      _ = u₀ * (g⁻¹ * h) := by group
  have hidx : Nat.card (X ⧸ C) = N := by
    have h1 : C.index * Nat.card C = Nat.card X := Subgroup.index_mul_card C
    have hpos : 0 < Nat.card C := Nat.card_pos
    rw [← Subgroup.index_eq_card]
    have : C.index * Nat.card C = N * Nat.card C := by rw [h1, ← hcent, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [hidx]; exact hN)
  intro u hu1 hu2
  obtain ⟨q, hq⟩ := hbij.2 ⟨u, hu1, hu2⟩
  induction q using Quotient.inductionOn with
  | _ g =>
  exact ⟨g, congrArg Subtype.val hq⟩

theorem k33InvFacts_top_of_data {X : Type} [Group X] [Finite X] (u₀ : X)
    (hconj : ∀ u : X, u ≠ 1 → u ^ 2 = 1 → ∃ g : X, g * u₀ * g⁻¹ = u)
    (Tl : List X) (hTl : ∀ x : X, (x * u₀ = u₀ * x ∧ x ^ 3 = 1) ↔ x ∈ Tl)
    (hmem : u₀ ∈ Subgroup.closure {x : X | x ∈ Tl})
    (hcenter : ∀ w : X, w * u₀ = u₀ * w → (∀ t ∈ Tl, t * w = w * t) → w = 1 ∨ w = u₀)
    (hcent : ∀ b : X, (∀ t ∈ Tl, b * t = t * b) → b = 1 ∨ b = u₀)
    (a b : X) (ha : a ∈ Tl) (hb : b ∈ Tl)
    (Ws : List (List Bool)) (hgen : ∀ t ∈ Tl, ∃ w ∈ Ws, t = evB a b w)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab2 : (a * b) ^ 2 ≠ 1) (hab4 : (a * b) ^ 4 = 1)
    (Pl : List (X × X))
    (hPl : ∀ x ∈ Tl, ∀ y ∈ Tl, x ≠ 1 → y ≠ 1 → (x * y) ^ 2 ≠ 1 → (x * y) ^ 4 = 1 →
      (x, y) ∈ Pl)
    (hPlc : Pl.length ≤ 24) :
    ∀ u : X, u ≠ 1 → u ^ 2 = 1 → K33InvFacts (⊤ : Subgroup X) u := by
  have hset : {g : X | g ∈ (⊤ : Subgroup X) ∧ g * u₀ = u₀ * g ∧ g ^ 3 = 1} = {x : X | x ∈ Tl} := by
    ext x
    constructor
    · rintro ⟨-, h1, h2⟩
      exact (hTl x).1 ⟨h1, h2⟩
    · intro hx
      exact ⟨Subgroup.mem_top _, ((hTl x).2 hx).1, ((hTl x).2 hx).2⟩
  have hsub : ∀ t ∈ Tl, t ∈ threeCoreCent (⊤ : Subgroup X) u₀ := fun t ht =>
    Subgroup.subset_closure (by rw [hset]; exact ht)
  have h0 : K33InvFacts (⊤ : Subgroup X) u₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold threeCoreCent
      rw [hset]
      exact hmem
    · intro w hw hcen
      exact hcenter w (threeCoreCent_comm hw) (fun t ht => hcen t (hsub t ht))
    · intro b' _ hcen
      exact hcent b' (fun t ht => hcen t (hsub t ht))
    · exact aut_le_eight hTl a b ha hb Ws hgen ha1 hb1 hab2 hab4 Pl hPl hPlc
  intro u hu1 hu2
  obtain ⟨g, hg⟩ := hconj u hu1 hu2
  rw [← hg]
  exact K33InvFacts.conj h0 g

section Transport

variable {G : Type} [Group G]

theorem k33Facts_of_mulEquiv {X : Type} [Group X] {K : Subgroup G} (e : ↥K ≃* X)
    (h : K33Facts (⊤ : Subgroup X)) : K33Facts K := by
  let f : X →* G := K.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.symm.injective
  have hfK : ∀ x : X, f x ∈ K := fun x => (e.symm x).2
  have hfe : ∀ k : ↥K, f (e k) = (k : G) := fun k => by simp [f]
  have hcardK : Nat.card ↥K = Nat.card X := Nat.card_congr e.toEquiv
  refine ⟨?_, ?_, ?_⟩
  · rw [hcardK]
    simpa [Subgroup.card_top] using h.card
  · obtain ⟨E, -, hE, hcard⟩ := h.rank
    refine ⟨E.map f, ?_, CFSG.SectionRank.isElemAbelian_map hE f, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact hfK x
    · rw [Subgroup.card_map_of_injective hf, hcard]
  · intro u hu hu1 hu2
    set u' : X := e ⟨u, hu⟩ with hu'
    have hfu : f u' = u := hfe ⟨u, hu⟩
    have hu'1 : u' ≠ 1 := by
      intro h1
      apply hu1
      rw [← hfu, h1, map_one]
    have hu'2 : u' ^ 2 = 1 := by
      apply hf
      rw [map_pow, hfu, hu2, map_one]
    have h' := h.inv u' (Subgroup.mem_top _) hu'1 hu'2
    have hEq : threeCoreCent K u = (threeCoreCent (⊤ : Subgroup X) u').map f := by
      unfold threeCoreCent
      rw [MonoidHom.map_closure]
      congr 1
      ext g
      constructor
      · rintro ⟨hg, h1, h2⟩
        refine ⟨e ⟨g, hg⟩, ⟨Subgroup.mem_top _, ?_, ?_⟩, hfe ⟨g, hg⟩⟩
        · apply hf
          rw [map_mul, map_mul, hfe, hfu]
          exact h1
        · apply hf
          rw [map_pow, hfe, map_one]
          exact h2
      · rintro ⟨x, ⟨-, h1, h2⟩, rfl⟩
        refine ⟨hfK x, ?_, ?_⟩
        · rw [← hfu, ← map_mul, ← map_mul, h1]
        · rw [← map_pow, h2, map_one]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hEq, ← hfu]
      exact Subgroup.mem_map_of_mem _ h'.mem
    · intro w hw hcen
      rw [hEq] at hw hcen
      obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
      have hc : ∀ v ∈ threeCoreCent (⊤ : Subgroup X) u', v * w₀ = w₀ * v := by
        intro v hv
        apply hf
        rw [map_mul, map_mul]
        exact hcen (f v) (Subgroup.mem_map_of_mem _ hv)
      rcases h'.center w₀ hw₀ hc with rfl | rfl
      · left; exact map_one f
      · right; exact hfu
    · intro b hb hcen
      rw [hEq] at hcen
      have hbf : f (e ⟨b, hb⟩) = b := hfe ⟨b, hb⟩
      have hc : ∀ v ∈ threeCoreCent (⊤ : Subgroup X) u', e ⟨b, hb⟩ * v = v * e ⟨b, hb⟩ := by
        intro v hv
        apply hf
        rw [map_mul, map_mul, hbf]
        exact hcen (f v) (Subgroup.mem_map_of_mem _ hv)
      rcases h'.centralizer (e ⟨b, hb⟩) (Subgroup.mem_top _) hc with h1 | h1
      · left
        rw [← hbf, h1, map_one]
      · right
        rw [← hbf, h1, hfu]
    · intro P hP
      let ι : ↥(threeCoreCent (⊤ : Subgroup X) u') ≃* ↥(threeCoreCent K u) :=
        (Subgroup.equivMapOfInjective _ f hf).trans (MulEquiv.subgroupCongr hEq.symm)
      let Φ : MulAut ↥(threeCoreCent K u) ≃* MulAut ↥(threeCoreCent (⊤ : Subgroup X) u') :=
        MulAut.congr ι.symm
      have hP' : IsPGroup 2 (P.map Φ.toMonoidHom) := hP.map _
      have := h'.aut _ hP'
      rwa [Subgroup.card_map_of_injective Φ.injective] at this

end Transport

end CFSG.QuasithinUnique.Unc25K1
