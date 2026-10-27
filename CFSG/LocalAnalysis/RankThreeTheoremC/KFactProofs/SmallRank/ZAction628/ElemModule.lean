module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.Coprime

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

section PartA

theorem elemMod_normal {Y M : Subgroup K} (hMn : ∀ x ∈ Y, ∀ m ∈ M, x * m * x⁻¹ ∈ M) :
    (M.subgroupOf Y).Normal :=
  ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact hMn g g.2 n hn⟩

abbrev elemMod_cg {Y M : Subgroup K} [(M.subgroupOf Y).Normal]
    [h : Fact (∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ M)] : CommGroup (↥Y ⧸ M.subgroupOf Y) :=
  { (inferInstance : Group (↥Y ⧸ M.subgroupOf Y)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with | _ a => ?_
      induction b using QuotientGroup.induction_on with | _ b => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
      have := h.out (b⁻¹ : ↥Y) (b⁻¹).2 (a⁻¹ : ↥Y) (a⁻¹).2
      simpa [mul_assoc] using this }

attribute [local instance] elemMod_cg

theorem elemMod_exp {f : ℕ} {Y M : Subgroup K} [(M.subgroupOf Y).Normal]
    (hexp : ∀ x ∈ Y, x ^ f ∈ M) (v : Additive (↥Y ⧸ M.subgroupOf Y)) : f • v = 0 := by
  obtain ⟨a, rfl⟩ := Additive.ofMul.surjective v
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  rw [← ofMul_pow, ← ofMul_one]
  congr 1
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
  exact hexp x x.2

abbrev elemMod_md {f : ℕ} {Y M : Subgroup K} [NeZero f] [(M.subgroupOf Y).Normal]
    [Fact (∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ M)] [h : Fact (∀ x ∈ Y, x ^ f ∈ M)] :
    Module (ZMod f) (Additive (↥Y ⧸ M.subgroupOf Y)) :=
  AddCommGroup.zmodModule (elemMod_exp h.out)

attribute [local instance] elemMod_md

@[expose] def elemMod_conjY (Y : Subgroup K) (g : K) (hg : g ∈ normalizer (Y : Set K)) :
    ↥Y →* ↥Y where
  toFun a := ⟨g * (a : K) * g⁻¹, (mem_set_normalizer_iff.mp hg (a : K)).mp a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[expose] def elemMod_conjQ {Y M : Subgroup K} [(M.subgroupOf Y).Normal] (g : K)
    (hgY : g ∈ normalizer (Y : Set K)) (hgM : g ∈ normalizer (M : Set K)) :
    (↥Y ⧸ M.subgroupOf Y) →* (↥Y ⧸ M.subgroupOf Y) :=
  QuotientGroup.map (M.subgroupOf Y) (M.subgroupOf Y) (elemMod_conjY Y g hgY) (by
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_comap, mem_subgroupOf]
    exact (mem_set_normalizer_iff.mp hgM (x : K)).mp hx)

theorem elemMod_conjQ_mk {Y M : Subgroup K} [(M.subgroupOf Y).Normal] (g : K)
    (hgY : g ∈ normalizer (Y : Set K)) (hgM : g ∈ normalizer (M : Set K)) (x : K) (hx : x ∈ Y)
    (hgx : g * x * g⁻¹ ∈ Y) :
    elemMod_conjQ g hgY hgM (QuotientGroup.mk ⟨x, hx⟩) = QuotientGroup.mk ⟨g * x * g⁻¹, hgx⟩ := rfl

theorem elemMod_conjQ_one {Y M : Subgroup K} [(M.subgroupOf Y).Normal]
    (hgY : (1 : K) ∈ normalizer (Y : Set K)) (hgM : (1 : K) ∈ normalizer (M : Set K))
    (a : ↥Y ⧸ M.subgroupOf Y) : elemMod_conjQ (1 : K) hgY hgM a = a := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  rw [show (QuotientGroup.mk x : ↥Y ⧸ M.subgroupOf Y) = QuotientGroup.mk ⟨(x : K), x.2⟩ from rfl,
    elemMod_conjQ_mk _ _ _ _ _ (by simpa using x.2)]
  congr 1
  exact Subtype.ext (by simp)

theorem elemMod_conjQ_mul {Y M : Subgroup K} [(M.subgroupOf Y).Normal] (g h : K)
    (hgY : g ∈ normalizer (Y : Set K)) (hgM : g ∈ normalizer (M : Set K))
    (hhY : h ∈ normalizer (Y : Set K)) (hhM : h ∈ normalizer (M : Set K))
    (hghY : g * h ∈ normalizer (Y : Set K)) (hghM : g * h ∈ normalizer (M : Set K))
    (a : ↥Y ⧸ M.subgroupOf Y) :
    elemMod_conjQ (g * h) hghY hghM a = elemMod_conjQ g hgY hgM (elemMod_conjQ h hhY hhM a) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  show QuotientGroup.mk _ = QuotientGroup.mk _
  congr 1
  exact Subtype.ext (by simp [elemMod_conjY, mul_assoc])

@[expose] noncomputable def elemMod_pi (Y M : Subgroup K) [(M.subgroupOf Y).Normal] (x : K) :
    Additive (↥Y ⧸ M.subgroupOf Y) :=
  open scoped Classical in
  if hx : x ∈ Y then Additive.ofMul (QuotientGroup.mk (⟨x, hx⟩ : ↥Y)) else Additive.ofMul 1

theorem elemMod_pi_of_mem {Y M : Subgroup K} [(M.subgroupOf Y).Normal] {x : K} (hx : x ∈ Y) :
    elemMod_pi Y M x = Additive.ofMul (QuotientGroup.mk (⟨x, hx⟩ : ↥Y)) := by
  simp [elemMod_pi, hx]

theorem exists_elemSection {f : ℕ} [Fact f.Prime] {Y M G : Subgroup K} (hMY : M ≤ Y)
    (hMn : ∀ x ∈ Y, ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hab : ∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ M) (hexp : ∀ x ∈ Y, x ^ f ∈ M)
    (hGY : G ≤ normalizer (Y : Set K)) (hGM : G ≤ normalizer (M : Set K)) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod f) W) (_ : Module.Finite (ZMod f) W)
      (π : K → W) (ρ : Representation (ZMod f) ↥G W),
      (∀ x ∈ Y, ∀ y ∈ Y, π (x * y) = π x + π y) ∧ (∀ x ∈ Y, π x = 0 ↔ x ∈ M) ∧
      (∀ w : W, ∃ x ∈ Y, π x = w) ∧ (∀ (g : ↥G), ∀ x ∈ Y, ρ g (π x) = π (g * x * g⁻¹)) := by
  haveI hN : (M.subgroupOf Y).Normal := elemMod_normal hMn
  haveI : Fact (∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ M) := ⟨hab⟩
  haveI : Fact (∀ x ∈ Y, x ^ f ∈ M) := ⟨hexp⟩
  haveI : NeZero f := ⟨(Fact.out : f.Prime).ne_zero⟩
  haveI hfin : Module.Finite (ZMod f) (Additive (↥Y ⧸ M.subgroupOf Y)) :=
    Module.Finite.of_finite
  have key : ∃ ρ : Representation (ZMod f) ↥G (Additive (↥Y ⧸ M.subgroupOf Y)),
      ∀ (g : ↥G), ∀ x ∈ Y, ρ g (elemMod_pi Y M x) = elemMod_pi Y M (g * x * g⁻¹) := by
    refine ⟨{ toFun := fun g => (MonoidHom.toAdditive
        (elemMod_conjQ (g : K) (hGY g.2) (hGM g.2))).toZModLinearMap f
              map_one' := ?_
              map_mul' := ?_ }, ?_⟩
    · apply LinearMap.ext
      intro w
      obtain ⟨a, rfl⟩ := Additive.ofMul.surjective w
      exact congrArg Additive.ofMul (elemMod_conjQ_one _ _ a)
    · intro g h
      apply LinearMap.ext
      intro w
      obtain ⟨a, rfl⟩ := Additive.ofMul.surjective w
      exact congrArg Additive.ofMul (elemMod_conjQ_mul (g : K) (h : K) (hGY g.2) (hGM g.2)
        (hGY h.2) (hGM h.2) (hGY (g * h).2) (hGM (g * h).2) a)
    · intro g x hx
      have hgx : (g : K) * x * ((g⁻¹ : ↥G) : K) ∈ Y :=
        (mem_set_normalizer_iff.mp (hGY g.2) x).mp hx
      rw [elemMod_pi_of_mem hx, elemMod_pi_of_mem hgx]
      rfl
  obtain ⟨ρ, hρ⟩ := key
  refine ⟨Additive (↥Y ⧸ M.subgroupOf Y), inferInstance, inferInstance, hfin, elemMod_pi Y M, ρ,
    ?_, ?_, ?_, hρ⟩
  · intro x hx y hy
    rw [elemMod_pi_of_mem (Y.mul_mem hx hy), elemMod_pi_of_mem hx, elemMod_pi_of_mem hy]
    rfl
  · intro x hx
    rw [elemMod_pi_of_mem hx, ofMul_eq_zero, QuotientGroup.eq_one_iff, mem_subgroupOf]
  · intro w
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    exact ⟨x, x.2, by rw [elemMod_pi_of_mem x.2]⟩

end PartA

theorem elemMod_exists_maximal {f : ℕ} [Fact f.Prime] {X N : Subgroup K} (hX : IsPGroup f X)
    (hNX : N ≤ X) (hXN : ¬ X ≤ N) :
    ∃ H : Subgroup K, N ≤ H ∧ ¬ X ≤ H ∧ (∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ H) ∧
      ∀ x ∈ X, x ^ f ∈ H := by
  haveI hnil : Group.IsNilpotent ↥X := hX.isNilpotent
  have hN' : N.subgroupOf X ≠ ⊤ := fun h => hXN (subgroupOf_eq_top.mp h)
  obtain ⟨H, hH, hNH⟩ := (eq_top_or_exists_le_coatom (N.subgroupOf X)).resolve_left hN'
  haveI hHn : H.Normal := Group.normalizerCondition_of_isNilpotent.normal_of_coatom H hH
  have hidx : H.index = f := hX.isCoatom_iff_index_eq_prime.mp hH
  have hcard : Nat.card (↥X ⧸ H) = f := by rw [← Subgroup.index_eq_card]; exact hidx
  haveI : IsCyclic (↥X ⧸ H) := isCyclic_of_prime_card hcard
  refine ⟨H.map X.subtype, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact ⟨⟨n, hNX hn⟩, hNH (mem_subgroupOf.mpr hn), rfl⟩
  · intro hXH
    apply hH.1
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := hXH y.2
    have : y' = y := Subtype.ext hyy
    rwa [← this]
  · intro x hx y hy
    refine ⟨⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹, ?_, rfl⟩
    show ((⟨x, hx⟩ : ↥X) * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹) ∈ H
    rw [← QuotientGroup.eq_one_iff]
    have hc : ∀ A B : ↥X ⧸ H, A * B = B * A := fun A B =>
      Std.Commutative.comm (op := (· * ·)) A B
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hc (QuotientGroup.mk ⟨x, hx⟩) (QuotientGroup.mk ⟨y, hy⟩)]
    group
  · intro x hx
    refine ⟨(⟨x, hx⟩ : ↥X) ^ f, ?_, rfl⟩
    show (⟨x, hx⟩ : ↥X) ^ f ∈ H
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
    exact pow_card_eq_one'

@[expose] def elemMod_M (f : ℕ) (X N : Subgroup K) : Subgroup K :=
  N ⊔ ⁅X, X⁆ ⊔ Subgroup.closure {x : K | ∃ y ∈ X, x = y ^ f}

theorem elemMod_M_le {f : ℕ} {X N : Subgroup K} (hNX : N ≤ X) : elemMod_M f X N ≤ X := by
  refine sup_le (sup_le hNX ?_) ?_
  · rw [commutator_le]
    intro a ha b hb
    exact X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
  · rw [closure_le]
    rintro _ ⟨y, hy, rfl⟩
    exact X.pow_mem hy f

theorem elemMod_N_le {f : ℕ} {X N : Subgroup K} : N ≤ elemMod_M f X N :=
  le_sup_left.trans le_sup_left

theorem elemMod_comm_mem {f : ℕ} {X N : Subgroup K} {x y : K} (hx : x ∈ X) (hy : y ∈ X) :
    x * y * x⁻¹ * y⁻¹ ∈ elemMod_M f X N :=
  (le_sup_right.trans le_sup_left : ⁅X, X⁆ ≤ elemMod_M f X N) (commutator_mem_commutator hx hy)

theorem elemMod_pow_mem {f : ℕ} {X N : Subgroup K} {y : K} (hy : y ∈ X) : y ^ f ∈ elemMod_M f X N :=
  (le_sup_right : Subgroup.closure {x : K | ∃ y ∈ X, x = y ^ f} ≤ elemMod_M f X N)
    (subset_closure ⟨y, hy, rfl⟩)

theorem elemMod_normalizer_comm {X : Subgroup K} {g : K} (hgX : g ∈ normalizer (X : Set K)) :
    g ∈ normalizer ((⁅X, X⁆ : Subgroup K) : Set K) := by
  rw [mem_normalizer_iff_map_conj_eq] at hgX ⊢
  rw [map_commutator, hgX]

theorem elemMod_normalizer_pow {f : ℕ} {X : Subgroup K} {g : K} (hgX : g ∈ normalizer (X : Set K)) :
    g ∈ normalizer ((Subgroup.closure {x : K | ∃ y ∈ X, x = y ^ f} : Subgroup K) : Set K) := by
  apply normalizer_le_normalizer_closure
  rw [mem_set_normalizer_iff]
  intro u
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨g * y * g⁻¹, (mem_set_normalizer_iff.mp hgX y).mp hy, ?_⟩
    simp [conj_pow]
  · rintro ⟨y, hy, hu⟩
    have hyg : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    refine ⟨g⁻¹ * y * g, (mem_set_normalizer_iff.mp hgX (g⁻¹ * y * g)).mpr (by rw [hyg]; exact hy),
      ?_⟩
    have hcp : (g⁻¹ * y * g) ^ f = g⁻¹ * y ^ f * g := by
      simpa using conj_pow (a := g⁻¹) (b := y) (i := f)
    rw [hcp, ← hu]
    group

theorem elemMod_normalizer_M {f : ℕ} {X N : Subgroup K} {g : K} (hgX : g ∈ normalizer (X : Set K))
    (hgN : g ∈ normalizer (N : Set K)) : g ∈ normalizer ((elemMod_M f X N : Subgroup K) : Set K) :=
  inf_normalizer_le_normalizer_sup _ _
    ⟨inf_normalizer_le_normalizer_sup _ _ ⟨hgN, elemMod_normalizer_comm hgX⟩,
      elemMod_normalizer_pow hgX⟩

theorem elemMod_not_dvd_card {f q : ℕ} (hf : f.Prime) (hq : q.Prime) (hqf : q ≠ f)
    {M X : Subgroup K} (hX : IsPGroup f X) (hMX : M ≤ X) : ¬ q ∣ Nat.card M := by
  haveI : Fact f.Prime := ⟨hf⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hX.to_le hMX)
  rw [hn]
  intro hdvd
  exact hqf ((Nat.prime_dvd_prime_iff_eq hq hf).mp (hq.dvd_of_dvd_pow hdvd))

theorem elemMod_mem_of_fixed {q : ℕ} [Fact q.Prime] {X M T N : Subgroup K}
    (hMX : M ≤ X) (hNM : N ≤ M) (hT : IsPGroup q T) (hTM : T ≤ normalizer (M : Set K))
    (hq : ¬ q ∣ Nat.card M)
    (hC : ∀ y ∈ X, (∀ t ∈ T, t * y = y * t) → y ∈ N) {x : K} (hx : x ∈ X)
    (hfix : ∀ t ∈ T, x⁻¹ * (t * x * t⁻¹) ∈ M) : x ∈ M := by
  obtain ⟨m, hm, hfixm⟩ := exists_fixed_in_coset hT hTM hq hfix
  have hxm : x * m ∈ N := hC (x * m) (X.mul_mem hx (hMX hm)) fun t ht =>
    mul_inv_eq_iff_eq_mul.mp (hfixm t ht)
  have h1 : x * m ∈ M := hNM hxm
  have h2 := M.mul_mem h1 (M.inv_mem hm)
  simpa using h2

theorem elemMod_mem_of_pi_eq {X M : Subgroup K} {W : Type} [AddCommGroup W] {π : K → W}
    (hadd : ∀ x ∈ X, ∀ y ∈ X, π (x * y) = π x + π y) (h0 : ∀ x ∈ X, π x = 0 ↔ x ∈ M)
    {x y : K} (hx : x ∈ X) (hy : y ∈ X) (hxy : π y = π x) : x⁻¹ * y ∈ M := by
  have hxy' : x⁻¹ * y ∈ X := X.mul_mem (X.inv_mem hx) hy
  have h1 := hadd x hx (x⁻¹ * y) hxy'
  rw [mul_inv_cancel_left, hxy] at h1
  exact (h0 _ hxy').mp (add_eq_left.mp h1.symm)

theorem elemMod_fix_zpowers {G : Type} [Group G] [Finite G] {R W : Type} [CommRing R]
    [AddCommGroup W] [Module R W] (ρ : Representation R G W) (g : G) (w : W) (hw : ρ g w = w)
    {t : G} (ht : t ∈ zpowers g) : ρ t w = w := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr ht)
  rw [← hn]
  clear hn ht
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, hw, ih]

theorem exists_module {p f : ℕ} {S X N : Subgroup K} {z : K} (h : Setup628 p f S X N z) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod f) W) (_ : Module.Finite (ZMod f) W)
      (ρ : Representation (ZMod f) ↥(S ⊔ zpowers z) W),
      Nontrivial W ∧
      (∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
        ∀ w : W, (∀ g : ↥(S ⊔ zpowers z), (g : K) ∈ S₀ → ρ g w = w) → w = 0) ∧
      (∀ w : W, ρ ⟨z, mem_sup_right (mem_zpowers z)⟩ w = w → w = 0) := by
  haveI : Fact f.Prime := ⟨h.hf⟩
  have hMX : elemMod_M f X N ≤ X := elemMod_M_le h.hNX
  have hXN' : X ≤ normalizer (N : Set K) := (normal_subgroupOf_iff_le_normalizer h.hNX).mp h.hNn
  have hMn : ∀ x ∈ X, ∀ m ∈ elemMod_M f X N, x * m * x⁻¹ ∈ elemMod_M f X N := fun x hx m hm =>
    (mem_set_normalizer_iff.mp (elemMod_normalizer_M (f := f) (le_normalizer hx) (hXN' hx)) m).mp hm
  have hGM : S ⊔ zpowers z ≤ normalizer ((elemMod_M f X N : Subgroup K) : Set K) := fun g hg =>
    elemMod_normalizer_M (h.hSX hg) (h.hSN hg)
  obtain ⟨W, i1, i2, i3, π, ρ, hadd, h0, hsurj, hρ⟩ := exists_elemSection (f := f) hMX hMn
    (fun x hx y hy => elemMod_comm_mem hx hy) (fun x hx => elemMod_pow_mem hx) h.hSX hGM
  have hfix : ∀ (g : ↥(S ⊔ zpowers z)) {x : K}, x ∈ X → ρ g (π x) = π x →
      x⁻¹ * (g * x * g⁻¹) ∈ elemMod_M f X N := by
    intro g x hx hg
    have hgx : (g : K) * x * ((g⁻¹ : ↥(S ⊔ zpowers z)) : K) ∈ X :=
      (mem_set_normalizer_iff.mp (h.hSX g.2) x).mp hx
    refine elemMod_mem_of_pi_eq hadd h0 hx hgx ?_
    rw [← hρ g x hx, hg]
  refine ⟨W, i1, i2, i3, ρ, ?_, ?_, ?_⟩
  · obtain ⟨H, hNH, hXH, hcommH, hpowH⟩ := elemMod_exists_maximal h.hX h.hNX h.hXN
    have hMH : elemMod_M f X N ≤ H := by
      refine sup_le (sup_le hNH ?_) ?_
      · exact commutator_le.mpr fun a ha b hb => hcommH a ha b hb
      · rw [closure_le]
        rintro _ ⟨y, hy, rfl⟩
        exact hpowH y hy
    have hex : ∃ x ∈ X, x ∉ elemMod_M f X N := by
      by_contra hcon
      push Not at hcon
      exact hXH fun x hx => hMH (hcon x hx)
    obtain ⟨x, hx, hxM⟩ := hex
    exact nontrivial_of_ne (π x) 0 fun h0' => hxM ((h0 x hx).mp h0')
  · intro S₀ hS₀S hS₀ne hzS₀ w hw
    obtain ⟨x, hx, rfl⟩ := hsurj w
    refine (h0 x hx).mpr ?_
    refine elemMod_mem_of_fixed (q := 2) (X := X) (T := S₀) hMX elemMod_N_le (h.hS.to_le hS₀S)
      (fun s hs => hGM (mem_sup_left (hS₀S hs)))
      (elemMod_not_dvd_card h.hf Nat.prime_two (Ne.symm h.hf2) h.hX hMX)
      (fun y hy hyc => h.hC S₀ hS₀S hS₀ne hzS₀ ⟨hy, mem_centralizer_iff.mpr hyc⟩) hx ?_
    intro t ht
    exact hfix ⟨t, mem_sup_left (hS₀S ht)⟩ hx (hw ⟨t, mem_sup_left (hS₀S ht)⟩ ht)
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := hsurj w
    refine (h0 x hx).mpr ?_
    haveI : Fact p.Prime := ⟨h.hp⟩
    have hzG : z ∈ S ⊔ zpowers z := mem_sup_right (mem_zpowers z)
    have hpz : IsPGroup p (zpowers z) :=
      IsPGroup.of_card_dvd_pow (n := 1)
        (by rw [Nat.card_zpowers, pow_one]; exact orderOf_dvd_of_pow_eq_one h.hzp)
    refine elemMod_mem_of_fixed (q := p) (X := X) (T := zpowers z) hMX elemMod_N_le hpz
      (fun t ht => hGM (mem_sup_right ht))
      (elemMod_not_dvd_card h.hf h.hp h.hfp.symm h.hX hMX)
      (fun y hy hyc => h.hCz ⟨hy, mem_centralizer_iff.mpr (by
        intro u hu
        rw [Set.mem_singleton_iff] at hu
        rw [hu]
        exact hyc z (mem_zpowers z))⟩) hx ?_
    intro t ht
    refine hfix ⟨t, mem_sup_right ht⟩ hx ?_
    refine elemMod_fix_zpowers ρ ⟨z, hzG⟩ (π x) hw ?_
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ht
    exact mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
