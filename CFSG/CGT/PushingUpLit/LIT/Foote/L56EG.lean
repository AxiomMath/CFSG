module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56EGAux
public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Diag
public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Mirror

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3
  (Theorem3Statement Frame SylowFrame exists_isSylowOf_le rightConjugate_le_rightConjugate)

variable {G : Type} [Group G] [Finite G]

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem false_of_mem_conj (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) (hTwo : TwoOrbit M J)
    {g : G} {T S : Subgroup G} (hgood : Good56 M J g)
    (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g))
    (hmax : ∀ h, Good56 M J h →
      (Nat.card ↥(eSub J h)).factorization 2 ≤ (Nat.card ↥(eSub J g)).factorization 2)
    (hS : SylowFrame J T S) (hncent : ¬ ∀ t ∈ T, ∀ v ∈ blockU J, t * v = v * t)
    {y : G} (hyJ : y ∈ J)
    (hyN : rightConjugate (S ⊓ Subgroup.normalizer (T : Set G)) y ≤
      S ⊓ Subgroup.normalizer ((S ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G))
    {u : G} (huT : u ∈ rightConjugate T y) (huW : u ∉ S ⊓ Subgroup.normalizer (T : Set G))
    (huM : u ∈ rightConjugate M g) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ := c.block
  have hg : g ∉ M := hgood.1
  obtain ⟨hTc, hTs, hQV, hQT⟩ := c.partC hA hz hgood hT hmax hS hncent
  have hTB : T ≤ rightConjugate J g := hT.le.trans inf_le_left
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hS.le_normalizer
  have hTU : T ≤ blockU (rightConjugate J g) := c.le_blockU_conj hA hz hgood hT hmax hS hncent
  have hTW : T ≤ S ⊓ Subgroup.normalizer (T : Set G) := le_inf hS.le Subgroup.le_normalizer
  have huSN : u ∈ S ⊓ Subgroup.normalizer
      ((S ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) :=
    hyN ((rightConjugate_le_rightConjugate hTW y) huT)
  have huS : u ∈ S := huSN.1
  have huNW : u ∈ Subgroup.normalizer
      ((S ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) := huSN.2
  have hu2 : u * u = 1 := by
    have h1 := hTs _ ((mem_rightConjugate_iff T y u).1 huT)
    have e : u * u = y⁻¹ * ((y * u * y⁻¹) * (y * u * y⁻¹)) * y := by group
    rw [e, h1]
    group
  have hu1 : u ≠ 1 := fun h =>
    huW (by rw [h]; exact (S ⊓ Subgroup.normalizer (T : Set G)).one_mem)
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hnB : u ∉ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) := by
    intro huB
    have hxle : rightConjugate T u ≤ T := by
      intro x hx
      have hx' : u * x * u⁻¹ ∈ T := (mem_rightConjugate_iff T u x).1 hx
      have hxB : x ∈ rightConjugate J g := (Subgroup.mem_normalizer_iff.1 huB x).2 (hTB hx')
      have hxW : x ∈ S ⊓ Subgroup.normalizer (T : Set G) :=
        (Subgroup.mem_normalizer_iff.1 huNW x).2 (hTW hx')
      exact c.inf_conj_le_of_sylowFrame hg hS hQV hTB ⟨hxB, hxW⟩
    have heq : rightConjugate T u = T :=
      Subgroup.eq_of_le_of_card_ge hxle (le_of_eq (rightConjugate_card T u).symm)
    have huNT : u ∈ Subgroup.normalizer (T : Set G) := (rightConjugate_eq_self_iff T u).1 heq
    exact huW ⟨huS, huNT⟩
  have hc₁ := c.transport g
  have hz₁ := hz.transport g
  have hTwo₁ := hTwo.transport g
  have hB := hJ.conj g
  have hne : rightConjugate (rightConjugate J g) u ≠ rightConjugate J g := fun h =>
    hnB ((rightConjugate_eq_self_iff _ u).1 h)
  have hBB' : ∀ b ∈ rightConjugate J g, ∀ b' ∈ rightConjugate (rightConjugate J g) u,
      b * b' = b' * b := by
    intro b hb b' hb'
    have hcomm := hc₁.commutator_conj_eq_bot huM hne
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hb
    exact (Subgroup.mem_centralizer_iff.1 this b' hb').symm
  have hcommδ : ∀ b ∈ rightConjugate J g, ∀ b'' ∈ rightConjugate J g,
      b'' * (u⁻¹ * b * u) = (u⁻¹ * b * u) * b'' := by
    intro b hb b'' hb''
    have hmem : u⁻¹ * b * u ∈ rightConjugate (rightConjugate J g) u := by
      rw [mem_rightConjugate_iff]
      have e : u * (u⁻¹ * b * u) * u⁻¹ = b := by group
      rw [e]
      exact hb
    exact hBB' b'' hb'' _ hmem
  set δ := diagHom (rightConjugate J g) u hcommδ with hδdef
  have hc₃ := c.transport (g * y)
  obtain ⟨J₄, hJ₄ne, hJ₄⟩ := hTwo.transport (g * y)
  have hJ₃eq : rightConjugate (rightConjugate J g) y = rightConjugate J (g * y) :=
    rightConjugate_mul J g y
  have hXN := hc₃.le_normalizer_blockU_sup hJ₄ne hJ₄
  obtain ⟨m₃, hm₃, hne₃⟩ := hc₃.exists_conj_ne
  have hJ₄eq : rightConjugate (rightConjugate J (g * y)) m₃ = J₄ :=
    (hJ₄ m₃ hm₃).resolve_left hne₃
  have hJ₃J₄ : ∀ a ∈ rightConjugate J (g * y), ∀ b ∈ J₄, a * b = b * a := by
    intro a ha b hb
    have hcomm := hc₃.commutator_conj_eq_bot hm₃ hne₃
    rw [hJ₄eq] at hcomm
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm ha
    exact (Subgroup.mem_centralizer_iff.1 this b hb).symm
  have hB₃ : QBlock (rightConjugate J (g * y)) := hJ.conj (g * y)
  have hB₄ : QBlock J₄ := by
    rw [← hJ₄eq]
    exact hB₃.conj m₃
  obtain ⟨hXc, hXs⟩ := sup_isElemAbelian hB₃.blockU_comm hB₃.blockU_sq_eq_one hB₄.blockU_comm
    hB₄.blockU_sq_eq_one (fun a ha b hb => hJ₃J₄ a (blockU_le _ ha) b (blockU_le _ hb))
  have huU₃ : u ∈ blockU (rightConjugate J (g * y)) := by
    have h1 : u ∈ rightConjugate (blockU (rightConjugate J g)) y :=
      (rightConjugate_le_rightConjugate hTU y) huT
    rw [← blockU_rightConjugate, hJ₃eq] at h1
    exact h1
  obtain ⟨X, hXdef⟩ : ∃ X : Subgroup G,
      X = blockU (rightConjugate J (g * y)) ⊔ blockU J₄ := ⟨_, rfl⟩
  rw [← hXdef] at hXN hXc hXs
  have huX : u ∈ X := by
    rw [hXdef]
    exact Subgroup.mem_sup_left huU₃
  have hXu : ∀ x ∈ X, x * u = u * x := fun x hx => hXc x hx u huX
  have hCu : Subgroup.centralizer ({u} : Set G) ≤ rightConjugate M (g * y) :=
    hc₃.centralizer_le_of_mem (blockU_le _ huU₃) ⟨1, by rw [pow_one, pow_two]; exact hu2⟩ hu1
  have hKu : ∀ k ∈ δ.range, k * u = u * k := by
    rintro _ ⟨b, rfl⟩
    exact (diagHom_comm hu2 b).symm
  have hZ2 : IsPGroup 2 ↥(zSub (rightConjugate M g) (g⁻¹ * z₀ * g)) := hc₁.isPGroup_zSub hz₁
  have hZ0 : zSub (rightConjugate M g) (g⁻¹ * z₀ * g) ≠ ⊥ := zSub_ne_bot hz₁
  have hZn : Subgroup.zpowers u ≤ Subgroup.normalizer
      ((zSub (rightConjugate M g) (g⁻¹ * z₀ * g) : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 (le_normalizer_zSub huM)
  have hu2' : IsPGroup 2 ↥(Subgroup.zpowers u) := isPGroup_zpowers_of_sq hu2 hu1
  have hfix := SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two
    hu2' hZ2 hZ0 hZn
  obtain ⟨⟨z, hzmem⟩, hz1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hfix
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  obtain ⟨hzZ, hzC⟩ := Subgroup.mem_inf.1 hzmem
  have huz : u * z = z * u := Subgroup.mem_centralizer_iff.1 hzC u (Subgroup.mem_zpowers u)
  have hzsq : z * z = 1 := hc₁.zSub_sq hz₁ hzZ
  have hzM₁ : Subgroup.centralizer ({z} : Set G) ≤ rightConjugate M g :=
    hc₁.centralizer_le hz₁ hzZ hz1
  have hzM₃ : z ∈ rightConjugate M (g * y) :=
    hCu (Subgroup.mem_centralizer_singleton_iff.2 huz.symm)
  have hzB : ∀ b ∈ rightConjugate J g, z * b = b * z := fun b hb =>
    hc₁.zSub_centralizes hz₁ hzZ (rightConjugate M g).one_mem
      (by rw [rightConjugate_one]; exact hb)
  have hzB' : ∀ b ∈ rightConjugate (rightConjugate J g) u, z * b = b * z := fun b hb =>
    hc₁.zSub_centralizes hz₁ hzZ huM hb
  have hKz : ∀ k ∈ δ.range, k * z = z * k := by
    rintro _ ⟨b, rfl⟩
    have hb := hzB b b.2
    have hw : z * (u⁻¹ * (b : G) * u) = (u⁻¹ * (b : G) * u) * z := hzB' _ (by
      rw [mem_rightConjugate_iff]
      have e : u * (u⁻¹ * (b : G) * u) * u⁻¹ = b := by group
      rw [e]
      exact b.2)
    show (b : G) * (u⁻¹ * b * u) * z = z * ((b : G) * (u⁻¹ * b * u))
    calc (b : G) * (u⁻¹ * b * u) * z = b * ((u⁻¹ * b * u) * z) := by group
      _ = b * (z * (u⁻¹ * b * u)) := by rw [hw]
      _ = (b * z) * (u⁻¹ * b * u) := by group
      _ = (z * b) * (u⁻¹ * b * u) := by rw [hb]
      _ = z * ((b : G) * (u⁻¹ * b * u)) := by group
  have hzX : ∀ x ∈ X, z * x * z⁻¹ ∈ X := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hXN hzM₃) x).1 hx
  have hKX : ∀ k ∈ δ.range, ∀ x ∈ X, k * x * k⁻¹ ∈ X := fun k hk x hx =>
    (Subgroup.mem_normalizer_iff.1
      (hXN (hCu (Subgroup.mem_centralizer_singleton_iff.2 (hKu k hk)))) x).1 hx
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = X ⊓ Subgroup.centralizer ({z} : Set G) := ⟨_, rfl⟩
  have hCmem : ∀ a, a ∈ C ↔ a ∈ X ∧ a * z = z * a := by
    intro a
    rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hKC' : ∀ k ∈ δ.range, k ∈ Subgroup.normalizer (C : Set G) := by
    have key := le_normalizer_of_forall (H := C) (K := δ.range) (fun k hk a ha => ?_)
    · exact fun k hk => key hk
    rw [hCmem] at ha ⊢
    refine ⟨hKX k hk a ha.1, ?_⟩
    have hkz := hKz k hk
    have hkz' : k⁻¹ * z = z * k⁻¹ := by
      calc k⁻¹ * z = k⁻¹ * (z * k) * k⁻¹ := by group
        _ = k⁻¹ * (k * z) * k⁻¹ := by rw [hkz]
        _ = z * k⁻¹ := by group
    calc k * a * k⁻¹ * z = k * a * (k⁻¹ * z) := by group
      _ = k * a * (z * k⁻¹) := by rw [hkz']
      _ = k * (a * z) * k⁻¹ := by group
      _ = k * (z * a) * k⁻¹ := by rw [ha.2]
      _ = (k * z) * a * k⁻¹ := by group
      _ = (z * k) * a * k⁻¹ := by rw [hkz]
      _ = z * (k * a * k⁻¹) := by group
  obtain ⟨J'', hJ''ne, hJ''⟩ := hTwo₁
  have hBu : rightConjugate (rightConjugate J g) u = J'' := (hJ'' u huM).resolve_left hne
  have hCK' : ∀ c' ∈ C, c' ∈ Subgroup.normalizer ((δ.range : Subgroup G) : Set G) := by
    have key := le_normalizer_of_forall (H := δ.range) (K := C) (fun c' hc' k hk => ?_)
    · exact fun c' hc' => key hc'
    obtain ⟨hc'X, hc'z⟩ := (hCmem c').1 hc'
    have hcu : c' * u = u * c' := hXu c' hc'X
    have hc'M : c' ∈ rightConjugate M g :=
      hzM₁ (Subgroup.mem_centralizer_singleton_iff.2 hc'z)
    have hc : (∀ b ∈ rightConjugate J g, c' * b * c'⁻¹ ∈ rightConjugate J g) ∨
        (∀ b ∈ rightConjugate J g, c' * b * c'⁻¹ ∈ rightConjugate (rightConjugate J g) u) := by
      rcases hJ'' c'⁻¹ ((rightConjugate M g).inv_mem hc'M) with h | h
      · left
        intro b hb
        have hN : c'⁻¹ ∈ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) :=
          (rightConjugate_eq_self_iff _ c'⁻¹).1 h
        have hN' := (Subgroup.normalizer _).inv_mem hN
        simpa using (Subgroup.mem_normalizer_iff.1 hN' b).1 hb
      · right
        intro b hb
        rw [hBu, ← h, mem_rightConjugate_iff]
        have e : c'⁻¹ * (c' * b * c'⁻¹) * c'⁻¹⁻¹ = b := by group
        rw [e]
        exact hb
    exact conj_mem_range_diagHom hu2 hBB' hcu hc k hk
  have hdich := diag_dichotomy hB δ hKC' hCK'
  have hKperf : ⁅δ.range, δ.range⁆ = δ.range := by
    have : Group.IsPerfect ↥(rightConjugate J g) := Subgroup.isPerfect_iff.2 hB.perfect
    have := Group.IsPerfect.range δ
    exact Subgroup.commutator_eq_self
  have hcentX : ∀ t (ht : t ∈ T), ∀ x ∈ X, δ ⟨t, hTB ht⟩ * x = x * δ ⟨t, hTB ht⟩ := by
    intro t ht x hx
    rcases hdich with hc | hb
    · have key := centralizes_of_centralizes_fixed hXc hXs hzsq hzX hKX hKz hKperf
        (fun k hk x hx hzx => hc k hk x ((hCmem x).2 ⟨hx, hzx.symm⟩))
      exact key _ ⟨⟨t, hTB ht⟩, rfl⟩ x hx
    · have hmem : δ ⟨t, hTB ht⟩ ∈ C := hb ⟨t, hTB ht⟩ (hTU ht)
      exact hXc _ ((hCmem _).1 hmem).1 x hx
  obtain ⟨t₀, ht₀, hq1⟩ : ∃ t ∈ T, t * (u⁻¹ * t * u) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply huW
    refine ⟨huS, ?_⟩
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun t ht => ?_)
    have h1 := hcon t ht
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hTs t ht)
    have h2 : u⁻¹ * t * u = t⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hti] at h2
    calc t * u = u * (u⁻¹ * t * u) := by group
      _ = u * t := by rw [h2]
  have hqW : t₀ * (u⁻¹ * t₀ * u) ∈ S ⊓ Subgroup.normalizer (T : Set G) := by
    refine (S ⊓ Subgroup.normalizer (T : Set G)).mul_mem (hTW ht₀) ?_
    refine (Subgroup.mem_normalizer_iff.1 huNW (u⁻¹ * t₀ * u)).2 ?_
    have e : u * (u⁻¹ * t₀ * u) * u⁻¹ = t₀ := by group
    rw [e]
    exact hTW ht₀
  have hqJ : t₀ * (u⁻¹ * t₀ * u) ∈ J := by
    have huTJ : u ∈ T ⊔ J := by
      rw [sup_comm]
      exact hS.sylow.le huS
    obtain ⟨t₁, ht₁, d, hd, htd⟩ := exists_mul_of_mem_sup hTN huTJ
    have hc1 : t₁⁻¹ * t₀ * t₁ = t₀ := by
      have := hTc t₀ ht₀ t₁ ht₁
      calc t₁⁻¹ * t₀ * t₁ = t₁⁻¹ * (t₀ * t₁) := by group
        _ = t₁⁻¹ * (t₁ * t₀) := by rw [this]
        _ = t₀ := by group
    have e : t₀ * (u⁻¹ * t₀ * u) = (t₀ * d⁻¹ * t₀⁻¹) * (t₀ * t₀) * d := by
      rw [← htd]
      calc t₀ * ((t₁ * d)⁻¹ * t₀ * (t₁ * d)) = t₀ * (d⁻¹ * (t₁⁻¹ * t₀ * t₁) * d) := by group
        _ = t₀ * (d⁻¹ * t₀ * d) := by rw [hc1]
        _ = (t₀ * d⁻¹ * t₀⁻¹) * (t₀ * t₀) * d := by group
    rw [e, hTs t₀ ht₀, mul_one]
    exact J.mul_mem ((Subgroup.mem_normalizer_iff.1 (hTN ht₀) d⁻¹).1 (J.inv_mem hd)) hd
  have hqV : t₀ * (u⁻¹ * t₀ * u) ∈ blockU J := hQV ⟨hqW, hqJ⟩
  have hq2 : (t₀ * (u⁻¹ * t₀ * u)) * (t₀ * (u⁻¹ * t₀ * u)) = 1 :=
    hJ.blockU_sq_eq_one _ hqV
  have hCq : Subgroup.centralizer ({t₀ * (u⁻¹ * t₀ * u)} : Set G) ≤ M :=
    c.centralizer_le_of_mem hqJ ⟨1, by rw [pow_one, pow_two]; exact hq2⟩ hq1
  have hVM₃ : blockU (rightConjugate J (g * y)) ≤ M := by
    intro x hx
    have hxX : x ∈ X := by
      rw [hXdef]
      exact Subgroup.mem_sup_left hx
    apply hCq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcentX t₀ ht₀ x hxX).symm
  have hVM : blockU (rightConjugate J g) ≤ M := by
    intro a ha
    have h1 : y⁻¹ * a * y ∈ blockU (rightConjugate J (g * y)) := by
      rw [← hJ₃eq, blockU_rightConjugate, mem_rightConjugate_iff]
      have e : y * (y⁻¹ * a * y) * y⁻¹ = a := by group
      rw [e]
      exact ha
    have h2 := hVM₃ h1
    have hy : y ∈ M := c.le hyJ
    have h3 := M.mul_mem (M.mul_mem hy h2) (M.inv_mem hy)
    have e : y * (y⁻¹ * a * y) * y⁻¹ = a := by group
    rwa [e] at h3
  exact c.false_of_blockU_conj_le hA hz hgood hT hmax hS hncent hVM

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
