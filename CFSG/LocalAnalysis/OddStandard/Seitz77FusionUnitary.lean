module

public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionMain
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionAlpha

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ComponentClassification CFSG.PSL3Four.Native CFSG.ABGLocalTools
  CFSG.ComponentClassification.PSL3Four CFSG.Open
open scoped commutatorElement

namespace Unitary

variable {G : Type*} [Group G]

theorem mem_sup_centralizer {B : Subgroup G} {x : G} (hx : x ∈ B ⊔ centralizer (B : Set G)) :
    ∃ a ∈ B, ∃ k ∈ centralizer (B : Set G), x = a * k := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ B, ∃ k ∈ centralizer (B : Set G), x = a * k}
      mul_mem' := by
        rintro _ _ ⟨a, ha, k, hk, rfl⟩ ⟨a', ha', k', hk', rfl⟩
        refine ⟨a * a', B.mul_mem ha ha', k * k', (centralizer _).mul_mem hk hk', ?_⟩
        have h : a' * k = k * a' := mem_centralizer_iff.mp hk a' ha'
        calc a * k * (a' * k') = a * (k * a') * k' := by group
          _ = a * (a' * k) * k' := by rw [h]
          _ = a * a' * (k * k') := by group
      one_mem' := ⟨1, B.one_mem, 1, (centralizer _).one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, k, hk, rfl⟩
        refine ⟨a⁻¹, B.inv_mem ha, k⁻¹, (centralizer _).inv_mem hk, ?_⟩
        have h : a * k = k * a := mem_centralizer_iff.mp hk a ha
        have h' : Commute a k := h
        rw [mul_inv_rev]
        exact (h'.inv_inv.eq).symm }
  have hle : B ⊔ centralizer (B : Set G) ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, (centralizer _).one_mem, by simp⟩)
      (fun k hk => ⟨1, B.one_mem, k, hk, by simp⟩)
  exact hle hx

theorem exists_eq_mul_of_mem_sup [Finite G] {B : Subgroup G} (hZ : Odd (Nat.card (center B)))
    {z : G} (hz : z ∈ B ⊔ centralizer (B : Set G)) (hz2 : z * z = 1) :
    ∃ α ∈ B, ∃ κ ∈ centralizer (B : Set G), α * α = 1 ∧ κ * κ = 1 ∧ z = α * κ := by
  obtain ⟨a, ha, k, hk, rfl⟩ := mem_sup_centralizer hz
  have hak : Commute a k := mem_centralizer_iff.mp hk a ha
  have h1 : a * a * (k * k) = 1 := by
    rw [← hz2]
    calc a * a * (k * k) = a * (a * k) * k := by group
      _ = a * (k * a) * k := by rw [hak.eq]
      _ = a * k * (a * k) := by group
  set c : G := a * a with hc
  have hcB : c ∈ B := B.mul_mem ha ha
  have hck : c = (k * k)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hcC : c ∈ centralizer (B : Set G) := by
    rw [hck]
    exact (centralizer _).inv_mem ((centralizer _).mul_mem hk hk)
  have hcZ : (⟨c, hcB⟩ : B) ∈ center B := by
    rw [mem_center_iff]
    intro b
    exact Subtype.ext (mem_centralizer_iff.mp hcC b.1 b.2)
  set n := Nat.card (center B) with hn
  have hcn : c ^ n = 1 := by
    have : (⟨⟨c, hcB⟩, hcZ⟩ : center B) ^ n = 1 := pow_card_eq_one'
    have h2 := congrArg (fun x : center B => ((x : B) : G)) this
    simpa using h2
  obtain ⟨m, hm⟩ := hZ
  have hα2 : a ^ n * a ^ n = 1 := by
    rw [← pow_add, show n + n = 2 * n by ring, pow_mul, sq]
    simpa [hc] using hcn
  have e1 : (a ^ n)⁻¹ * (a * k) = (c ^ m)⁻¹ * k := by
    have : (a ^ n)⁻¹ * a = (c ^ m)⁻¹ := by
      rw [hm, hc, ← sq, ← pow_mul, show a ^ (2 * m + 1) = a ^ (2 * m) * a by rw [pow_succ]]
      group
    calc (a ^ n)⁻¹ * (a * k) = ((a ^ n)⁻¹ * a) * k := by group
      _ = (c ^ m)⁻¹ * k := by rw [this]
  have hck' : k * k = c⁻¹ := by rw [hck, inv_inv]
  have hck_comm : Commute c k := by
    have h0 : Commute (k * k)⁻¹ k := ((Commute.refl k).mul_left (Commute.refl k)).inv_left
    rw [hck]
    exact h0
  have hxk : Commute ((c ^ m)⁻¹) k := (hck_comm.pow_left m).inv_left
  refine ⟨a ^ n, B.pow_mem ha n, (a ^ n)⁻¹ * (a * k), ?_, hα2, ?_, ?_⟩
  · rw [e1]
    exact (centralizer _).mul_mem ((centralizer _).inv_mem ((centralizer _).pow_mem hcC m)) hk
  · rw [e1]
    have h5 : (c ^ m)⁻¹ * k * ((c ^ m)⁻¹ * k) = (c ^ m)⁻¹ * (c ^ m)⁻¹ * (k * k) := by
      calc (c ^ m)⁻¹ * k * ((c ^ m)⁻¹ * k) = (c ^ m)⁻¹ * (k * (c ^ m)⁻¹) * k := by group
        _ = (c ^ m)⁻¹ * ((c ^ m)⁻¹ * k) * k := by rw [← hxk.eq]
        _ = (c ^ m)⁻¹ * (c ^ m)⁻¹ * (k * k) := by group
    rw [h5, hck']
    have h6 : (c ^ m)⁻¹ * (c ^ m)⁻¹ * c⁻¹ = (c ^ n)⁻¹ := by
      rw [hm, pow_succ, pow_mul', sq]
      group
    rw [h6, hcn, inv_one]
  · group

theorem exists_involution_of_relIndex_le [Finite G] {Q N : Subgroup G} (hQ : IsPGroup 2 Q)
    (h8 : 8 ≤ Nat.card Q) (hidx : (Q ⊓ N).relIndex Q ≤ 4) :
    ∃ z ∈ Q ⊓ N, z * z = 1 ∧ z ≠ 1 := by
  have hmul := Subgroup.card_mul_index ((Q ⊓ N).subgroupOf Q)
  have hrel : ((Q ⊓ N).subgroupOf Q).index = (Q ⊓ N).relIndex Q := rfl
  have hcard : 2 ≤ Nat.card ((Q ⊓ N).subgroupOf Q) := by
    by_contra hlt
    have h1 : Nat.card ((Q ⊓ N).subgroupOf Q) ≤ 1 := by omega
    have h2 : Nat.card Q ≤ 1 * 4 := by
      calc Nat.card Q = Nat.card ((Q ⊓ N).subgroupOf Q) * ((Q ⊓ N).subgroupOf Q).index :=
            hmul.symm
        _ ≤ 1 * 4 := Nat.mul_le_mul h1 (hrel ▸ hidx)
    omega
  have hcard' : Nat.card (↥(Q ⊓ N)) = Nat.card ((Q ⊓ N).subgroupOf Q) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Q ⊓ N ≤ Q)).toEquiv.symm
  have hP : IsPGroup 2 (↥(Q ⊓ N)) := hQ.to_inf_left
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have h2dvd : 2 ∣ Nat.card (↥(Q ⊓ N)) := by
    rcases k with _ | k
    · have : Nat.card (↥(Q ⊓ N)) = 1 := by simpa using hk
      omega
    · rw [hk]
      exact dvd_pow_self 2 (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Q ⊓ N)) 2 h2dvd
  refine ⟨x, x.2, ?_, ?_⟩
  · have h1 : x ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx] at this
    have h2 := congrArg (fun y : ↥(Q ⊓ N) => (y : G)) h1
    simpa [sq] using h2
  · intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx
    omega

theorem exists_pgroup_le_of_eight_dvd [Finite G] {H : Subgroup G} (h8 : 8 ∣ Nat.card H) :
    ∃ Q : Subgroup G, Q ≤ H ∧ IsPGroup 2 Q ∧ 8 ≤ Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
  have hS := Sylow.card_eq_multiplicity S
  have h3 : 3 ≤ (Nat.card H).factorization 2 := by
    have h8' : 2 ^ 3 ∣ Nat.card H := by simpa using h8
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h8'
  have hinj : Function.Injective H.subtype := H.subtype_injective
  refine ⟨(S : Subgroup H).map H.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.2
  · exact IsPGroup.of_card (n := (Nat.card H).factorization 2)
      (by rw [Subgroup.card_map_of_injective hinj]; exact hS)
  · rw [Subgroup.card_map_of_injective hinj, hS]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (Nat.card H).factorization 2 := Nat.pow_le_pow_right (by norm_num) h3

theorem eq_of_commuting_involutions [Finite G] {C : Subgroup G}
    (hcyc : ∀ S : Sylow 2 C, IsCyclic S) {x y : G} (hx : x ∈ C) (hy : y ∈ C)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) : x = 1 ∨ y = 1 ∨ x = y := by
  classical
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hx1, hy1, hxy'⟩ := hcon
  let E : Subgroup G := Subgroup.closure ({x, y} : Set G)
  have hEC : E ≤ C := (Subgroup.closure_le C).2 (by
    intro a ha
    rcases ha with rfl | ha
    · exact hx
    · rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hy)
  have h1 : ∀ g ∈ ({x, y} : Set G), ∀ h ∈ ({x, y} : Set G), g * h = h * g := by
    intro g hg h hh
    rcases hg with rfl | hg <;> rcases hh with rfl | hh
    · rfl
    · rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hxy
    · rw [Set.mem_singleton_iff] at hg; rw [hg]; exact hxy.symm
    · rw [Set.mem_singleton_iff] at hg hh; rw [hg, hh]
  have hE1 : E ≤ centralizer ({x, y} : Set G) :=
    (Subgroup.closure_le _).2 (fun g hg => mem_centralizer_iff.2 (fun k hk => h1 k hk g hg))
  have hEcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := by
    intro g hg h hh
    have hg' := mem_centralizer_iff.mp (hE1 hg)
    have hE2 : E ≤ centralizer ({g} : Set G) :=
      (Subgroup.closure_le _).2 (fun k hk => mem_centralizer_singleton_iff.2 (hg' k hk))
    exact (mem_centralizer_singleton_iff.mp (hE2 hh)).symm
  have hEinv : ∀ g ∈ E, g * g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | ha
      · exact hx2
      · rw [Set.mem_singleton_iff] at ha; rw [ha]; exact hy2
    | one => simp
    | mul a b ha hb iha ihb =>
      have hab : a * b = b * a := hEcomm a ha b hb
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = a * a * (b * b) := by group
        _ = 1 := by rw [iha, ihb, one_mul]
    | inv a ha iha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [iha, inv_one]
  have hpg : IsPGroup 2 (E.subgroupOf C) := by
    intro g
    refine ⟨1, ?_⟩
    have hgE : ((g : C) : G) ∈ E := g.2
    apply Subtype.ext; apply Subtype.ext
    simpa [sq] using hEinv _ hgE
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  have hSx : (⟨x, hx⟩ : C) ∈ (S : Subgroup C) := hS (by
    show x ∈ E
    exact Subgroup.subset_closure (by simp))
  have hSy : (⟨y, hy⟩ : C) ∈ (S : Subgroup C) := hS (by
    show y ∈ E
    exact Subgroup.subset_closure (by simp))
  have : IsCyclic (S : Subgroup C) := hcyc S
  let _ : Fintype (S : Subgroup C) := Fintype.ofFinite _
  let X : (S : Subgroup C) := ⟨⟨x, hx⟩, hSx⟩
  let Y : (S : Subgroup C) := ⟨⟨y, hy⟩, hSy⟩
  have hcard := IsCyclic.card_pow_eq_one_le (α := (S : Subgroup C)) (n := 2) (by norm_num)
  have hX2 : X ^ 2 = 1 := by
    apply Subtype.ext; apply Subtype.ext; simpa [sq, X] using hx2
  have hY2 : Y ^ 2 = 1 := by
    apply Subtype.ext; apply Subtype.ext; simpa [sq, Y] using hy2
  have hcoe : ∀ w w' : (S : Subgroup C), w = w' → ((w : C) : G) = ((w' : C) : G) :=
    fun w w' h => by rw [h]
  have hXne : X ≠ 1 := fun h => hx1 (by simpa [X] using hcoe _ _ h)
  have hYne : Y ≠ 1 := fun h => hy1 (by simpa [Y] using hcoe _ _ h)
  have hXY : X ≠ Y := fun h => hxy' (by simpa [X, Y] using hcoe _ _ h)
  have hsub : ({1, X, Y} : Finset (S : Subgroup C)) ⊆
      Finset.univ.filter (fun a : (S : Subgroup C) => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · exact hX2
    · exact hY2
  have h3 : ({1, X, Y} : Finset (S : Subgroup C)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hXY
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hXne.symm, hYne.symm⟩
  have := Finset.card_le_card hsub
  omega

theorem unitary_core [Finite G]
    {A : Subgroup G} {t g : G}
    (htC : t ∈ centralizer (A : Set G)) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hZ : Odd (Nat.card (center A)))
    (hcycK : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic S)
    (hN : centralizer ({t} : Set G) ≤ normalizer (A : Set G))
    (hF6 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ normalizer (A : Set G) →
        (Q ⊓ (A ⊔ centralizer (A : Set G))).relIndex Q ≤ 4)
    (hF8 : ∀ c ∈ A ⊓ centralizer ({g⁻¹ * t * g} : Set G), c * c = 1 →
        ∃ b ∈ A, b * (g⁻¹ * t * g) * b⁻¹ = (g⁻¹ * t * g) * c)
    (h8 : 8 ∣ Nat.card ↥(A ⊓ centralizer ({g⁻¹ * t * g} : Set G)))
    (hout : g⁻¹ * t * g ∉ A)
    (h3 : ∀ x ∈ A, x * x = 1 → x ≠ 1 → ∀ h : G, h⁻¹ * t * h ≠ x) :
    ∃ c ∈ A, c * c = 1 ∧ c ≠ 1 ∧ ∃ h : G, h⁻¹ * t * h = c * t := by
  classical
  set t' : G := g⁻¹ * t * g with ht'def
  set C₁ : Subgroup G := A ⊓ centralizer ({t'} : Set G) with hC₁
  let X₀ : Subgroup G := C₁.map (MulAut.conj g).toMonoidHom
  have hX₀card : Nat.card X₀ = Nat.card C₁ :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨Q, hQX, hQp, hQ8⟩ := exists_pgroup_le_of_eight_dvd (H := X₀) (by rw [hX₀card]; exact h8)
  have hXt : ∀ x ∈ X₀, x * t = t * x := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y * t' = t' * y := mem_centralizer_singleton_iff.mp hy.2
    show g * y * g⁻¹ * t = t * (g * y * g⁻¹)
    calc g * y * g⁻¹ * t = g * (y * t') * g⁻¹ := by simp only [ht'def]; group
      _ = g * (t' * y) * g⁻¹ := by rw [hy']
      _ = t * (g * y * g⁻¹) := by simp only [ht'def]; group
  have hQN : Q ≤ normalizer (A : Set G) := fun x hx =>
    hN (mem_centralizer_singleton_iff.mpr (hXt x (hQX hx)))
  obtain ⟨z₀, hz₀mem, hz₀2, hz₀1⟩ := exists_involution_of_relIndex_le hQp hQ8 (hF6 Q hQp hQN)
  have hz₀X : z₀ ∈ X₀ := hQX hz₀mem.1
  obtain ⟨z, hzC₁, hzdef⟩ := hz₀X
  have hzdef' : g * z * g⁻¹ = z₀ := hzdef
  have hz₀t : z₀ * t = t * z₀ := hXt z₀ ⟨z, hzC₁, hzdef⟩
  obtain ⟨α, hα, κ, hκ, hα2, hκ2, hz₀ακ⟩ := exists_eq_mul_of_mem_sup hZ hz₀mem.2 hz₀2
  have hαt : α * t = t * α := mem_centralizer_iff.mp htC α hα
  have hκt : κ * t = t * κ := by
    have : α * (κ * t) = α * (t * κ) := by
      calc α * (κ * t) = (α * κ) * t := by group
        _ = z₀ * t := by rw [← hz₀ακ]
        _ = t * z₀ := hz₀t
        _ = t * (α * κ) := by rw [hz₀ακ]
        _ = (t * α) * κ := by group
        _ = (α * t) * κ := by rw [hαt]
        _ = α * (t * κ) := by group
    exact mul_left_cancel this
  have hκcases : κ = 1 ∨ κ = t := by
    rcases eq_of_commuting_involutions hcycK hκ htC hκ2 ht2 hκt with h | h | h
    · exact Or.inl h
    · exact absurd h ht1
    · exact Or.inr h
  have hzA : z ∈ A := hzC₁.1
  have hz2 : z * z = 1 := by
    calc z * z = g⁻¹ * (g * z * g⁻¹ * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * (z₀ * z₀) * g := by rw [hzdef']
      _ = 1 := by rw [hz₀2]; group
  obtain ⟨b, hbA, hb⟩ := hF8 z hzC₁ hz2
  have hconj : (g * b⁻¹ * g⁻¹)⁻¹ * t * (g * b⁻¹ * g⁻¹) = t * z₀ := by
    calc (g * b⁻¹ * g⁻¹)⁻¹ * t * (g * b⁻¹ * g⁻¹) = g * (b * t' * b⁻¹) * g⁻¹ := by
          simp only [ht'def]; group
      _ = g * (t' * z) * g⁻¹ := by rw [hb]
      _ = t * (g * z * g⁻¹) := by simp only [ht'def]; group
      _ = t * z₀ := by rw [hzdef']
  rcases hκcases with hκ1 | hκt'
  · have hz₀α : z₀ = α := by rw [hz₀ακ, hκ1, mul_one]
    have hz₀A : z₀ ∈ A := hz₀α ▸ hα
    refine ⟨z₀, hz₀A, hz₀2, hz₀1, g * b⁻¹ * g⁻¹, ?_⟩
    rw [hconj]
    exact (mem_centralizer_iff.mp htC z₀ hz₀A).symm
  · exfalso
    have hz₀α : z₀ = α * t := by rw [hz₀ακ, hκt']
    have htz₀ : t * z₀ = α := by
      calc t * z₀ = t * (α * t) := by rw [hz₀α]
        _ = (t * α) * t := by group
        _ = (α * t) * t := by rw [hαt]
        _ = α * (t * t) := by group
        _ = α := by rw [ht2, mul_one]
    have hα1 : α ≠ 1 := by
      intro h1
      have hz₀t' : z₀ = t := by rw [hz₀α, h1, one_mul]
      apply hout
      have hzt' : z = t' := by
        calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
          _ = g⁻¹ * z₀ * g := by rw [hzdef']
          _ = t' := by rw [hz₀t']
      rw [← hzt']
      exact hzA
    exact h3 α hα hα2 hα1 (g * b⁻¹ * g⁻¹) (by rw [hconj, htz₀])

end Unitary

theorem eight_dvd_card_of_solvable_outer {G : Type*} [Group G]
    [Finite G] {B : Subgroup G} (hB : commutator ↥B = ⊤) (hZ : Odd (Nat.card (center ↥B)))
    (e : ↥B ⧸ center ↥B ≃* ↥PSL3Four.S) {y : G} (hy : y ∈ normalizer (B : Set G))
    (hy2 : y * y = 1) (hout : y ∉ B ⊔ centralizer (B : Set G))
    (hsolv : Group.IsSolvable ↥(B ⊓ centralizer ({y} : Set G))) :
    8 ∣ Nat.card ↥(B ⊓ centralizer ({y} : Set G)) := by
  obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom RankTwoL3Four.HypII.l34AutModel hB e
  have hψy2 : ψ ⟨y, hy⟩ * ψ ⟨y, hy⟩ = 1 := by
    have h1 : (⟨y, hy⟩ : ↥(normalizer (B : Set G))) * ⟨y, hy⟩ = 1 := Subtype.ext hy2
    rw [← map_mul, h1, map_one]
  have hy'S : (ψ ⟨y, hy⟩ : Equiv.Perm (Fin 42)) ∉ S := fun hS =>
    hout ((L34.mem_sup_centralizer_iff hψ hy).2 hS)
  have hle : B ⊓ centralizer ({y} : Set G) ≤ B := inf_le_left
  let π : ↥(B ⊓ centralizer ({y} : Set G)) →* ↥(centralizerBar B y) :=
    ((QuotientGroup.mk' (center ↥B)).comp (Subgroup.inclusion hle)).codRestrict
      (centralizerBar B y) fun a => ⟨Subgroup.inclusion hle a, a.2, rfl⟩
  have hπ : Function.Surjective π := by
    rintro ⟨_, c, hc, rfl⟩
    exact ⟨⟨c, hc⟩, rfl⟩
  have hbar : Group.IsSolvable ↥(centralizerBar B y) := Group.isSolvable_of_surjective hπ
  have hdvd : Nat.card ↥(centralizerBar B y) ∣ Nat.card ↥(B ⊓ centralizer ({y} : Set G)) :=
    Subgroup.card_dvd_of_surjective hπ
  have hx2 : orderOf (ψ ⟨y, hy⟩) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hψy2) fun h => hy'S (by rw [h]; exact S.one_mem)
  have hcard : Nat.card ↥(centralizerBar B y) = 72 := by
    rcases (PSL3Four.orderOf_eq_two_iff _).1 hx2 with h | h | h | h
    · exact absurd (PSL3Four.mem_S_of_isConj₁ h) hy'S
    · exfalso
      obtain ⟨u, hu, hyu⟩ := PSL3Four.eq_conj_of_isConj h
      obtain ⟨e'⟩ := L34.centralizerBar_equiv hZ hψ hy hy2 hu hyu
      have e'' : centralizerBar B y ≃* ↥C₂ := e'
      have := PSL3Four.isSimpleGroup_C₂
      obtain ⟨a, b, hab⟩ := PSL3Four.exists_mul_ne_C₂
      have hsC : Group.IsSolvable ↥C₂ :=
        Group.isSolvable_of_isSolvable_injective (f := e''.symm.toMonoidHom) e''.symm.injective
      exact hab (IsSimpleGroup.comm_iff_isSolvable.2 hsC a b)
    · exfalso
      obtain ⟨u, hu, hyu⟩ := PSL3Four.eq_conj_of_isConj h
      obtain ⟨e'⟩ := L34.centralizerBar_equiv hZ hψ hy hy2 hu hyu
      have e'' : centralizerBar B y ≃* ↥C₃ := e'
      have := PSL3Four.isSimpleGroup_C₃
      obtain ⟨a, b, hab⟩ := PSL3Four.exists_mul_ne_C₃
      have hsC : Group.IsSolvable ↥C₃ :=
        Group.isSolvable_of_isSolvable_injective (f := e''.symm.toMonoidHom) e''.symm.injective
      exact hab (IsSimpleGroup.comm_iff_isSolvable.2 hsC a b)
    · obtain ⟨u, hu, hyu⟩ := PSL3Four.eq_conj_of_isConj h
      obtain ⟨e'⟩ := L34.centralizerBar_equiv hZ hψ hy hy2 hu hyu
      have e'' : centralizerBar B y ≃* ↥C₄ := e'
      rw [Nat.card_congr e''.toEquiv, PSL3Four.card_C₄]
  rw [hcard] at hdvd
  exact (show 8 ∣ 72 by norm_num).trans hdvd

theorem unitaryResidualFalse_of_certificates :
    UnitaryResidualFalse := by
  classical
  intro G _ _ A h d hmax hex hall
  obtain ⟨V₁, V₂, hR⟩ := h.exists_radicals d
  have F := h.facts
  obtain ⟨e⟩ := h.nonempty_equiv_S
  obtain ⟨t', ht'P, hc, hne⟩ := hex
  obtain ⟨hnot, hsolv⟩ := hall t' ht'P hc hne
  have ht'2 : t' * t' = 1 := d.mul_self_of_isConj hc
  have ht'N : t' ∈ normalizer (A : Set G) := d.P_le_normalizer ht'P
  obtain ⟨c₀, hc₀⟩ := isConj_iff.mp hc
  have hg : (c₀⁻¹)⁻¹ * d.t * c₀⁻¹ = t' := by rw [inv_inv]; exact hc₀
  have h8 := eight_dvd_card_of_solvable_outer h.commutator_eq_top h.odd e ht'N ht'2 hnot hsolv
  have ht1 : d.t ≠ 1 := by
    intro h1
    have := d.sector.t_order
    rw [h1, orderOf_one] at this
    omega
  have hcore := Unitary.unitary_core (A := A) (t := d.t) (g := c₀⁻¹) d.t_mem_K d.t_mul_self ht1
    h.odd h.cyc (centralizer_t_facts d.sector).1
    (fun Q hQ hQN => (two_part_outer_le h.commutator_eq_top e hQ hQN).1)
    (by rw [hg]; exact fun c hc hc2 => F.outer_fuse t' ht'N ht'2 hnot c hc hc2)
    (by rw [hg]; exact h8)
    (by rw [hg]; exact fun hA => hnot (Subgroup.mem_sup_left hA))
    (fun x hx hx2 hx1 h' hh' => F.not_isConj_of_mem d hR hx
      (isConj_iff.mpr ⟨h'⁻¹, by rw [← hh']; group⟩))
  obtain ⟨c, hcA, hc2, hc1, h', hh'⟩ := hcore
  have hα : d.Alpha := F.alpha_of_exists_mul_t d hR hcA hc2 hc1
    (isConj_iff.mpr ⟨h'⁻¹, by rw [← hh']; group⟩)
  have hdvd : 2 ∣ d.P.index := F.two_dvd_index d hR hα
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hPT⟩ := d.hP.isPGroup.exists_le_sylow
  have hTP : (T : Subgroup G) = d.P := hmax T T.isPGroup' hPT
  exact T.not_dvd_index (hTP ▸ hdvd)

theorem alpha_of_certificates
    {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (h : Hyp G A) (d : Datum A) :
    ∃ t' ∈ d.P ⊓ centralizer (d.P : Set G), IsConj d.t t' ∧ t' ≠ d.t :=
  alpha unitaryResidualFalse_of_certificates h d

end CFSG.OddStandard.Seitz77
