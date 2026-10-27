module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarPerm
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartEmb
public import CFSG.LocalAnalysis.OddStandard.AltStdSecSwapDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS2a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm

@[expose] def IsNearPerm {n : ℕ} (σ : Perm (Fin n)) : Prop :=
  5 ≤ (fixFin σ).card ∧ (fixFin σ).card ≠ 6

variable {G : Type*} [Group G]

structure NearData (z : G) (n : ℕ) where
  S : Subgroup G
  ι : Perm (Fin n) ≃* S
  π : centralizer ({z} : Set G) →* Perm (Fin n)
  sq : z * z = 1
  ne_one : z ≠ 1
  le : S ≤ centralizer ({z} : Set G)
  π_ι : ∀ σ, π ⟨ι σ, le (ι σ).2⟩ = σ
  π_z : π ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ = 1
  ker : ∀ x : centralizer ({z} : Set G), π x = 1 → (x : G) = 1 ∨ (x : G) = z
  swap_mem : ∀ τ : Perm (Fin n), τ.IsSwap → (ι τ : G) ∈ Partners z
  near : ∀ x : centralizer ({z} : Set G), (x : G) ∈ Partners z → IsNearPerm (π x) →
    (π x).IsSwap ∧ (x : G) = ι (π x)

namespace NearData

variable {z : G} {n : ℕ}

theorem mem_centralizer_of_partner {a : G} (ha : a ∈ Partners z) :
    a ∈ centralizer ({z} : Set G) :=
  mem_centralizer_singleton_iff.2 ha.2.2

theorem self_mem_centralizer (z : G) : z ∈ centralizer ({z} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

variable (D : NearData z n)

theorem ι_mem (σ : Perm (Fin n)) : (D.ι σ : G) ∈ centralizer ({z} : Set G) := D.le (D.ι σ).2

theorem ι_mul (σ τ : Perm (Fin n)) : (D.ι (σ * τ) : G) = D.ι σ * D.ι τ := by
  rw [map_mul]; rfl

theorem ι_one : (D.ι 1 : G) = 1 := by rw [map_one]; rfl

theorem ι_injective {σ τ : Perm (Fin n)} (h : (D.ι σ : G) = D.ι τ) : σ = τ :=
  D.ι.injective (Subtype.ext h)

theorem ι_comm (σ : Perm (Fin n)) : (D.ι σ : G) * z = z * D.ι σ :=
  mem_centralizer_singleton_iff.1 (D.ι_mem σ)

theorem z_notMem : z ∉ D.S := by
  intro hz
  obtain ⟨σ, hσ⟩ := D.ι.surjective ⟨z, hz⟩
  have h1 : D.π ⟨D.ι σ, D.ι_mem σ⟩ = σ := D.π_ι σ
  have h2 : (⟨D.ι σ, D.ι_mem σ⟩ : centralizer ({z} : Set G)) =
      ⟨z, self_mem_centralizer z⟩ :=
    Subtype.ext (show (D.ι σ : G) = z from congrArg Subtype.val hσ)
  rw [h2, D.π_z] at h1
  apply D.ne_one
  have : (D.ι σ : G) = z := by rw [hσ]
  rw [← this, ← h1, D.ι_one]

theorem eq_or (x : centralizer ({z} : Set G)) :
    (x : G) = D.ι (D.π x) ∨ (x : G) = z * D.ι (D.π x) := by
  set y : centralizer ({z} : Set G) := x * (⟨D.ι (D.π x), D.ι_mem _⟩)⁻¹ with hy
  have hπ : D.π y = 1 := by
    rw [hy, map_mul, map_inv, D.π_ι, mul_inv_cancel]
  rcases D.ker y hπ with h | h
  · left
    have : (x : G) * (D.ι (D.π x) : G)⁻¹ = 1 := h
    exact mul_inv_eq_one.1 this
  · right
    have : (x : G) * (D.ι (D.π x) : G)⁻¹ = z := h
    calc (x : G) = ((x : G) * (D.ι (D.π x) : G)⁻¹) * D.ι (D.π x) := by group
      _ = z * D.ι (D.π x) := by rw [this]

theorem π_congr {x y : G} (hxy : x = y) (hx : x ∈ centralizer ({z} : Set G))
    (hy : y ∈ centralizer ({z} : Set G)) : D.π ⟨x, hx⟩ = D.π ⟨y, hy⟩ := by
  subst hxy; rfl

theorem π_z_mul (x : centralizer ({z} : Set G)) :
    D.π (⟨z, self_mem_centralizer z⟩ * x) = D.π x := by
  rw [map_mul, D.π_z, one_mul]

theorem card_centralizer_pair {a : G} (ha : a ∈ centralizer ({z} : Set G)) :
    Nat.card (centralizer ({z, a} : Set G)) =
      2 * Nat.card (centralizer ({D.π ⟨a, ha⟩} : Set (Perm (Fin n)))) := by
  have hle : centralizer ({z, a} : Set G) ≤ centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (by simp)
  set f : centralizer ({z, a} : Set G) →* Perm (Fin n) :=
    D.π.comp (Subgroup.inclusion hle) with hf
  have hza : z * a = a * z := (mem_centralizer_singleton_iff.1 ha).symm
  have hz2 : z ∈ centralizer ({z, a} : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | rfl
    · rfl
    · exact hza.symm
  have hker : f.ker = zpowers ⟨z, hz2⟩ := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      rcases D.ker _ hx with h | h
      · have : x = 1 := Subtype.ext h
        rw [this]; exact one_mem _
      · have : x = ⟨z, hz2⟩ := Subtype.ext h
        rw [this]; exact mem_zpowers _
    · intro hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      rw [map_zpow]
      have : f ⟨z, hz2⟩ = 1 := D.π_z
      rw [this, one_zpow]
  have hord : orderOf (⟨z, hz2⟩ : centralizer ({z, a} : Set G)) = 2 := by
    rw [Subgroup.orderOf_mk]
    apply orderOf_eq_prime
    · rw [pow_two]; exact D.sq
    · exact D.ne_one
  have hcardker : Nat.card f.ker = 2 := by
    rw [hker, Nat.card_zpowers, hord]
  have hrange : f.range = centralizer ({D.π ⟨a, ha⟩} : Set (Perm (Fin n))) := by
    ext σ
    constructor
    · rintro ⟨x, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have hxa : a * x = x * a := (mem_centralizer_iff.1 x.2) a (by simp)
      have : (⟨a, ha⟩ : centralizer ({z} : Set G)) * Subgroup.inclusion hle x =
          Subgroup.inclusion hle x * ⟨a, ha⟩ := Subtype.ext hxa
      simp only [hf, MonoidHom.coe_comp, Function.comp_apply]
      rw [← map_mul, ← map_mul, this]
    · intro hσ
      rw [mem_centralizer_singleton_iff] at hσ
      have hea : a = D.ι (D.π ⟨a, ha⟩) ∨ a = z * D.ι (D.π ⟨a, ha⟩) := D.eq_or ⟨a, ha⟩
      have haσ : a * D.ι σ = D.ι σ * a := by
        rcases hea with h | h
        · rw [h, ← D.ι_mul, ← D.ι_mul, hσ]
        · rw [h]
          calc z * (D.ι (D.π ⟨a, ha⟩) : G) * D.ι σ = z * D.ι (D.π ⟨a, ha⟩ * σ) := by
                rw [D.ι_mul, mul_assoc]
            _ = z * D.ι (σ * D.π ⟨a, ha⟩) := by rw [hσ]
            _ = (z * D.ι σ) * D.ι (D.π ⟨a, ha⟩) := by rw [D.ι_mul, mul_assoc]
            _ = (D.ι σ * z) * D.ι (D.π ⟨a, ha⟩) := by rw [D.ι_comm σ]
            _ = D.ι σ * (z * D.ι (D.π ⟨a, ha⟩)) := by rw [mul_assoc]
      have hι : (D.ι σ : G) ∈ centralizer ({z, a} : Set G) := by
        rw [mem_centralizer_iff]
        intro y hy
        rcases hy with rfl | rfl
        · exact (D.ι_comm σ).symm
        · exact haσ
      refine ⟨⟨D.ι σ, hι⟩, ?_⟩
      simp only [hf, MonoidHom.coe_comp, Function.comp_apply]
      exact D.π_ι σ
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange, hcardker] at h1
  exact h1.symm

@[expose] def conjCent (z g : G) :
    centralizer ({g * z * g⁻¹} : Set G) →* centralizer ({z} : Set G) where
  toFun x := ⟨g⁻¹ * x * g, by
    rw [mem_centralizer_singleton_iff]
    have hx := mem_centralizer_singleton_iff.1 x.2
    calc g⁻¹ * x * g * z = g⁻¹ * ((x : G) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hx]
      _ = z * (g⁻¹ * x * g) := by group⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp only [Subgroup.coe_mul]; group

theorem conjCent_apply (z g : G) (x : centralizer ({g * z * g⁻¹} : Set G)) :
    (conjCent z g x : G) = g⁻¹ * x * g := rfl

@[expose] noncomputable def conjEquiv (D : NearData z n) (g : G) :
    Perm (Fin n) ≃* ↥(D.S.map (MulAut.conj g).toMonoidHom) :=
  D.ι.trans (D.S.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)

theorem conjEquiv_apply (D : NearData z n) (g : G) (σ : Perm (Fin n)) :
    ((D.conjEquiv g σ : ↥(D.S.map (MulAut.conj g).toMonoidHom)) : G) = g * D.ι σ * g⁻¹ := rfl

@[expose] noncomputable def conj (D : NearData z n) (g : G) : NearData (g * z * g⁻¹) n where
  S := D.S.map (MulAut.conj g).toMonoidHom
  ι := D.conjEquiv g
  π := D.π.comp (conjCent z g)
  sq := by
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [D.sq]; group
  ne_one := fun h => D.ne_one (by
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  le := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hxz := mem_centralizer_singleton_iff.1 (D.le hx)
    show g * x * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * z * g⁻¹) = g * (x * z) * g⁻¹ := by group
      _ = g * (z * x) * g⁻¹ := by rw [hxz]
      _ = g * z * g⁻¹ * (g * x * g⁻¹) := by group
  π_ι σ := by
    show D.π (conjCent z g ⟨_, _⟩) = σ
    convert D.π_ι σ using 2
    apply Subtype.ext
    rw [conjCent_apply]
    show g⁻¹ * ((D.conjEquiv g σ : ↥(D.S.map (MulAut.conj g).toMonoidHom)) : G) * g = D.ι σ
    rw [conjEquiv_apply]; group
  π_z := by
    show D.π (conjCent z g ⟨g * z * g⁻¹, _⟩) = 1
    have : conjCent z g ⟨g * z * g⁻¹, self_mem_centralizer _⟩ =
        ⟨z, self_mem_centralizer z⟩ := by
      apply Subtype.ext
      rw [conjCent_apply]; group
    rw [this, D.π_z]
  ker x hx := by
    rcases D.ker _ hx with h | h
    · left
      rw [conjCent_apply] at h
      calc (x : G) = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · right
      rw [conjCent_apply] at h
      calc (x : G) = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * z * g⁻¹ := by rw [h]
  swap_mem τ hτ := by
    show ((D.conjEquiv g τ : ↥(D.S.map (MulAut.conj g).toMonoidHom)) : G) ∈ _
    rw [mem_partners_conj_iff, conjEquiv_apply]
    have : g⁻¹ * (g * (D.ι τ : G) * g⁻¹) * g = D.ι τ := by group
    rw [this]
    exact D.swap_mem τ hτ
  near x hx hnear := by
    have hx' : ((conjCent z g x : centralizer ({z} : Set G)) : G) ∈ Partners z := by
      rw [conjCent_apply]
      exact (mem_partners_conj_iff g z x).1 hx
    obtain ⟨hsw, heq⟩ := D.near _ hx' hnear
    refine ⟨hsw, ?_⟩
    show (x : G) = ((D.conjEquiv g (D.π (conjCent z g x)) :
      ↥(D.S.map (MulAut.conj g).toMonoidHom)) : G)
    have heq' : g⁻¹ * (x : G) * g = D.ι (D.π (conjCent z g x)) := heq
    rw [conjEquiv_apply, ← heq']
    group

theorem conj_ι_apply (D : NearData z n) (g : G) (σ : Perm (Fin n)) :
    ((D.conj g).ι σ : G) = g * D.ι σ * g⁻¹ := D.conjEquiv_apply g σ

theorem nonempty_of_isConj (D : NearData z n) {d : G} (hd : IsConj z d) :
    Nonempty (NearData d n) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hd
  rw [← hg]
  exact ⟨D.conj g⟩

theorem π_mul_self {x : centralizer ({z} : Set G)} (hx : (x : G) * x = 1) :
    D.π x * D.π x = 1 := by
  rw [← map_mul]
  have : x * x = 1 := Subtype.ext hx
  rw [this, map_one]

theorem π_ne_one {x : centralizer ({z} : Set G)} (h1 : (x : G) ≠ 1) (hz : (x : G) ≠ z) :
    D.π x ≠ 1 := fun h => (D.ker x h).elim h1 hz

theorem isSwap_symm (hn : 7 ≤ n) {d d' : G} (D : NearData d n) (D' : NearData d' n)
    (hd' : d' ∈ Partners d) (hsw : (D.π ⟨d', mem_centralizer_of_partner hd'⟩).IsSwap) :
    (D'.π ⟨d, mem_centralizer_of_partner (Partners.symm hd')⟩).IsSwap := by
  have h1 := D.card_centralizer_pair (mem_centralizer_of_partner hd')
  have h2 := D'.card_centralizer_pair (mem_centralizer_of_partner (Partners.symm hd'))
  rw [nat_card_centralizer_of_isSwap hsw, Set.pair_comm] at h1
  rw [h1] at h2
  have h3 : Nat.card (centralizer ({D'.π ⟨d, mem_centralizer_of_partner (Partners.symm hd')⟩} :
      Set (Perm (Fin n)))) = 2 * (Fintype.card (Fin n) - 2).factorial := by omega
  refine isSwap_of_nat_card_centralizer (by simpa using hn) (D'.π_mul_self D.sq)
    (D'.π_ne_one D.ne_one hd'.2.1.symm) h3

theorem fixFin_card_add_support_card (σ : Perm (Fin n)) :
    (fixFin σ).card + σ.support.card = n := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => σ i = i)
  have hs : σ.support = Finset.univ.filter (fun i => ¬ σ i = i) := by
    ext i; simp [mem_support]
  rw [hs]
  simpa [fixFin] using h

theorem isNearPerm_of_isSwap (hn : 11 ≤ n) {σ : Perm (Fin n)} (hσ : σ.IsSwap) : IsNearPerm σ := by
  have h := fixFin_card_add_support_card σ
  rw [card_support_eq_two.2 hσ] at h
  constructor <;> omega

theorem isNearPerm_mul_of_isSwap (hn : 11 ≤ n) {τ τ' : Perm (Fin n)} (hτ : τ.IsSwap)
    (hτ' : τ'.IsSwap) (hc : τ' * τ = τ * τ') (hne : τ' ≠ τ) : IsNearPerm (τ * τ') := by
  have hd : τ.Disjoint τ' := by
    intro x
    by_cases hx : τ x = x
    · exact Or.inl hx
    · exact Or.inr (fixes_of_comm_swap hτ hτ' hc hne hx)
  have h := fixFin_card_add_support_card (τ * τ')
  rw [hd.card_support_mul, card_support_eq_two.2 hτ, card_support_eq_two.2 hτ'] at h
  constructor <;> omega

omit [Group G] in
theorem ofSubtype_comm_of_fix {σ₁ : Perm (Fin n)} (s : Perm {i // σ₁ i = i}) :
    Perm.ofSubtype s * σ₁ = σ₁ * Perm.ofSubtype s := by
  apply Equiv.ext
  intro x
  simp only [Perm.mul_apply]
  by_cases hx : σ₁ x = x
  · rw [hx, ofSubtype_apply_of_mem s hx]
    exact ((s ⟨x, hx⟩).2).symm
  · have hx' : ¬ σ₁ (σ₁ x) = σ₁ x := fun h => hx (σ₁.injective h)
    rw [ofSubtype_apply_of_not_mem s hx', ofSubtype_apply_of_not_mem s hx]

theorem isSwap_of_swap_partners (hn : 11 ≤ n) {d d₁ d₂ : G} (D : NearData d n)
    (D₁ : NearData d₁ n) (h₁ : d₁ ∈ Partners d) (h₂ : d₂ ∈ Partners d)
    (hs₁ : (D.π ⟨d₁, mem_centralizer_of_partner h₁⟩).IsSwap)
    (hs₂ : (D.π ⟨d₂, mem_centralizer_of_partner h₂⟩).IsSwap)
    (h12 : d₂ * d₁ = d₁ * d₂) (hne : d₂ ≠ d₁) :
    (D₁.π ⟨d₂, mem_centralizer_singleton_iff.2 h12⟩).IsSwap := by
  classical
  set σ₁ := D.π ⟨d₁, mem_centralizer_of_partner h₁⟩ with hσ₁
  set σ₂ := D.π ⟨d₂, mem_centralizer_of_partner h₂⟩ with hσ₂
  obtain ⟨-, he₁⟩ := D.near ⟨d₁, mem_centralizer_of_partner h₁⟩ h₁ (isNearPerm_of_isSwap hn hs₁)
  obtain ⟨-, he₂⟩ := D.near ⟨d₂, mem_centralizer_of_partner h₂⟩ h₂ (isNearPerm_of_isSwap hn hs₂)
  change d₁ = D.ι σ₁ at he₁
  change d₂ = D.ι σ₂ at he₂
  have hc : σ₂ * σ₁ = σ₁ * σ₂ := by
    rw [hσ₁, hσ₂, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h12
  have hne' : σ₂ ≠ σ₁ := fun h => hne (by rw [he₂, he₁, h])
  have hsupp : ∀ x, σ₂ x ≠ x → σ₁ x = x := fun x hx => by
    by_contra h
    exact hx (fixes_of_comm_swap hs₁ hs₂ hc hne' h)
  have hmem : ∀ s : Perm {i // σ₁ i = i},
      (D.ι (Perm.ofSubtype s) : G) ∈ centralizer ({d₁} : Set G) := by
    intro s
    rw [mem_centralizer_singleton_iff, he₁, ← D.ι_mul, ← D.ι_mul, ofSubtype_comm_of_fix]
  set f : Perm {i // σ₁ i = i} →* G :=
    D.S.subtype.comp (D.ι.toMonoidHom.comp Perm.ofSubtype) with hf
  set Ψ : Perm {i // σ₁ i = i} →* Perm (Fin n) := D₁.π.comp (f.codRestrict _ hmem) with hΨ
  have hΨapp : ∀ s, Ψ s = D₁.π ⟨D.ι (Perm.ofSubtype s), hmem s⟩ := fun s => rfl
  have hdC : d ∈ centralizer ({d₁} : Set G) := mem_centralizer_singleton_iff.2 h₁.2.2.symm
  set τ := D₁.π ⟨d, hdC⟩ with hτdef
  have hτ : τ.IsSwap := isSwap_symm (by omega) D D₁ h₁ hs₁
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    rw [hΨapp] at hs
    rcases D₁.ker _ hs with h | h
    · have h' : D.ι (Perm.ofSubtype s) = D.ι 1 := by
        apply Subtype.ext
        rw [D.ι_one]; exact h
      have := D.ι.injective h'
      exact Perm.ofSubtype_injective (by rw [this, map_one])
    · exfalso
      have h' : Perm.ofSubtype s = σ₁ := D.ι_injective (by rw [← he₁]; exact h)
      obtain ⟨p, q, hpq, hpqe⟩ := hs₁
      have hp : σ₁ p ≠ p := by rw [hpqe, swap_apply_left]; exact hpq.symm
      have := DFunLike.congr_fun h' p
      rw [ofSubtype_apply_of_not_mem s hp] at this
      exact hp this.symm
  have hcomm : ∀ s, Ψ s * τ = τ * Ψ s := by
    intro s
    rw [hΨapp, hτdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (D.ι_comm _)
  have hneΨ : ∀ s, Ψ s ≠ τ := by
    intro s hs
    rw [hΨapp, hτdef] at hs
    have h1 : D₁.π (⟨D.ι (Perm.ofSubtype s), hmem s⟩ * (⟨d, hdC⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, hs, mul_inv_cancel]
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right D.sq
    rcases D₁.ker _ h1 with h | h
    · apply D.z_notMem
      have : (D.ι (Perm.ofSubtype s) : G) * d⁻¹ = 1 := h
      have h2 : (D.ι (Perm.ofSubtype s) : G) = d := by
        rw [hdinv] at this
        calc (D.ι (Perm.ofSubtype s) : G) = (D.ι (Perm.ofSubtype s) : G) * d * d := by
              rw [mul_assoc, D.sq, mul_one]
          _ = d := by rw [this, one_mul]
      have hm : (D.ι (Perm.ofSubtype s) : G) ∈ D.S := (D.ι _).2
      rwa [h2] at hm
    · apply D.z_notMem
      have : (D.ι (Perm.ofSubtype s) : G) * d⁻¹ = d₁ := h
      rw [hdinv, he₁] at this
      have h2 : (D.ι (Perm.ofSubtype s) : G)⁻¹ * D.ι σ₁ = d := by
        rw [← this]; group
      have hm : (D.ι (Perm.ofSubtype s) : G)⁻¹ * D.ι σ₁ ∈ D.S :=
        mul_mem (inv_mem (D.ι _).2) (D.ι _).2
      rwa [h2] at hm
  have hcard : Fintype.card {i // σ₁ i = i} = Fintype.card (Fin n) - 2 := card_fix_swap hs₁
  simp only [Fintype.card_fin] at hcard
  have hαβ : Fintype.card (Fin n) = Fintype.card {i // σ₁ i = i} + 2 := by
    rw [hcard, Fintype.card_fin]; omega
  set s₂ : Perm {i // σ₁ i = i} := σ₂.subtypePerm (fun x => fix_iff_of_comm hc x) with hs₂def
  have hof : Perm.ofSubtype s₂ = σ₂ := ofSubtype_subtypePerm _ hsupp
  have hs₂swap : s₂.IsSwap := by
    rw [← card_support_eq_two]
    have h1 := support_ofSubtype s₂
    rw [hof] at h1
    rw [← Finset.card_map (Function.Embedding.subtype _), ← h1, card_support_eq_two.2 hs₂]
  obtain ⟨τ', hτ's, hτ'c, hτ'ne, hΨs⟩ := embedding_swap_cases hαβ (by omega) Ψ hinj hτ hcomm
    hneΨ hs₂swap
  have hΨd : Ψ s₂ = D₁.π ⟨d₂, mem_centralizer_singleton_iff.2 h12⟩ := by
    rw [hΨapp]
    exact D₁.π_congr (by rw [hof, ← he₂]) _ _
  rw [hΨd] at hΨs
  have hnear : IsNearPerm (D₁.π ⟨d₂, mem_centralizer_singleton_iff.2 h12⟩) := by
    rcases hΨs with h | h
    · rw [h]; exact isNearPerm_of_isSwap hn hτ's
    · rw [h]; exact isNearPerm_mul_of_isSwap hn hτ hτ's hτ'c hτ'ne
  have h₂' : d₂ ∈ Partners d₁ := Partners.of_isConj h₁ h₂.1 hne h12
  exact (D₁.near _ h₂' hnear).1

end NearData

end CFSG.OddStandard.AltStdSec
