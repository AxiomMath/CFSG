module

public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.HardMathSupport.Solomon.Coordinator.B0TDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.B0TSylow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

theorem SuzSections.of_injective {D D' : Type} [Group D] [Group D'] (h : SuzSections D)
    (g : D' →* D) (hg : Function.Injective g) : SuzSections D' := by
  intro P S _ _ _ f hf hnab
  refine h (P.map g) S (f.comp (P.equivMapOfInjective g hg).symm.toMonoidHom) (hf.comp ?_) hnab
  exact (P.equivMapOfInjective g hg).symm.surjective

theorem SuzSections.of_surjective {D D' : Type} [Group D] [Group D'] (h : SuzSections D)
    (g : D →* D') (hg : Function.Surjective g) : SuzSections D' := by
  intro P S _ _ _ f hf hnab
  refine h (P.comap g) S (f.comp (g.subgroupComap P)) (hf.comp ?_) hnab
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := hg x
  exact ⟨⟨y, hx⟩, rfl⟩

theorem card_map_mk_eq_relIndex {Y : Type} [Group Y] [Finite Y] (D N : Subgroup Y) [N.Normal] :
    Nat.card (D.map (QuotientGroup.mk' N)) = N.relIndex D := by
  set f' := (QuotientGroup.mk' N).subgroupMap D with hf'
  have hker : f'.ker = N.subgroupOf D := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : (QuotientGroup.mk' N) (x : Y) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).1 h'
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 h)
  have hsurj : Function.Surjective f' := MonoidHom.subgroupMap_surjective _ _
  have h1 := Subgroup.index_ker f'
  rw [hker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top] at h1
  exact h1.symm

theorem relIndex_mul_card {Y : Type} [Group Y] [Finite Y] {D N : Subgroup Y} (hND : N ≤ D) :
    N.relIndex D * Nat.card N = Nat.card D := by
  have h := Subgroup.card_mul_index (N.subgroupOf D)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hND).toEquiv] at h
  rw [mul_comm]
  exact h

theorem commutator_eq_bot_of_centralizes {Y : Type} [Group Y] {D B N : Subgroup Y} [N.Normal]
    (hDB : ⁅D, B⁆ = D)
    (hBN : ∀ n ∈ N, ∀ b ∈ B, n * b = b * n) : ⁅D, N⁆ = ⊥ := by
  have hBN' : ⁅B, N⁆ = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [Subgroup.commutator_le]
    intro b hb n hn
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (hBN n hn b hb).symm
  have h1 : ⁅⁅B, N⁆, D⁆ = ⊥ := by rw [hBN', Subgroup.commutator_bot_left]
  have h2 : ⁅⁅N, D⁆, B⁆ = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc ⁅⁅N, D⁆, B⁆ ≤ ⁅N, B⁆ := Subgroup.commutator_mono_left (Subgroup.commutator_le_left N D)
      _ = ⊥ := by rw [Subgroup.commutator_comm, hBN']
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := D) (H₂ := B) (H₃ := N) h1 h2
  rwa [hDB] at h3

open scoped IsMulCommutative in
theorem false_of_central_two_group {Y : Type} [Group Y] [Finite Y] {D B N : Subgroup Y}
    (hDB : ⁅D, B⁆ = D) (hDn : D.Normal) (hN : N ≤ D) (hN1 : N ≠ ⊥) (hN2 : IsPGroup 2 N)
    (hcent : ⁅D, N⁆ = ⊥) (hBN : ∀ n ∈ N, ∀ b ∈ B, n * b = b * n)
    (hodd : Odd (N.relIndex D)) : False := by
  classical
  set N' : Subgroup D := N.subgroupOf D with hN'
  have hcen : ∀ x ∈ N', ∀ y : D, y * x = x * y := by
    intro x hx y
    have hxN : (x : Y) ∈ N := hx
    have : ⁅(y : Y), (x : Y)⁆ ∈ ⁅D, N⁆ := Subgroup.commutator_mem_commutator y.2 hxN
    rw [hcent, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact Subtype.ext this
  have : IsMulCommutative N' :=
    ⟨⟨fun a b => Subtype.ext (hcen _ b.2 (a : D))⟩⟩
  let ψ : D →* N' := MonoidHom.transfer (MonoidHom.id N')
  have key : ∀ g : D, ∀ (k : ℕ) (g₀ : D), g₀⁻¹ * g ^ k * g₀ ∈ N' → g₀⁻¹ * g ^ k * g₀ = g ^ k := by
    intro g k g₀ hk
    have hc := hcen _ hk g₀
    have h2 : g ^ k * g₀ = (g₀⁻¹ * g ^ k * g₀) * g₀ := by
      calc g ^ k * g₀ = g₀ * (g₀⁻¹ * g ^ k * g₀) := by group
        _ = _ := hc
    exact (mul_right_cancel h2).symm
  have hψ : ∀ g : D, ((ψ g : N') : D) = g ^ N'.index := by
    intro g
    have := MonoidHom.transfer_eq_pow (MonoidHom.id N') g (key g)
    rw [show ψ g = _ from this]
    rfl
  set K : Subgroup Y := ψ.ker.map D.subtype with hK
  have hle : ⁅D, B⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro d hd b hb
    have hd2 : b * d⁻¹ * b⁻¹ ∈ D := hDn.conj_mem _ (D.inv_mem hd) b
    refine ⟨⟨⁅d, b⁆, ?_⟩, ?_, rfl⟩
    · have : ⁅d, b⁆ = d * (b * d⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact D.mul_mem hd hd2
    · have e1 : (⟨⁅d, b⁆, by
          have : ⁅d, b⁆ = d * (b * d⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
          rw [this]
          exact D.mul_mem hd hd2⟩ : D) = (⟨d, hd⟩ : D) * ⟨b * d⁻¹ * b⁻¹, hd2⟩ :=
        Subtype.ext (by simp [commutatorElement_def, mul_assoc])
      rw [SetLike.mem_coe, MonoidHom.mem_ker, e1, map_mul]
      refine Subtype.ext (Subtype.ext ?_)
      have h1 := hψ ⟨d, hd⟩
      have h2 := hψ ⟨b * d⁻¹ * b⁻¹, hd2⟩
      have hdk : (d : Y) ^ N'.index ∈ N := by
        have := (ψ ⟨d, hd⟩).2
        have h3 : (((ψ ⟨d, hd⟩ : N') : D) : Y) = d ^ N'.index := by rw [h1]; rfl
        rw [← h3]
        exact this
      have hc := hBN _ hdk b hb
      show (((ψ ⟨d, hd⟩ : N') : D) : Y) * (((ψ ⟨b * d⁻¹ * b⁻¹, hd2⟩ : N') : D) : Y) = 1
      rw [h1, h2]
      show d ^ N'.index * (b * d⁻¹ * b⁻¹) ^ N'.index = 1
      rw [conj_pow, inv_pow]
      calc d ^ N'.index * (b * (d ^ N'.index)⁻¹ * b⁻¹)
          = (d ^ N'.index * b) * (d ^ N'.index)⁻¹ * b⁻¹ := by group
        _ = (b * d ^ N'.index) * (d ^ N'.index)⁻¹ * b⁻¹ := by rw [hc]
        _ = 1 := by group
  have hker : ∀ x : D, ψ x = 1 := by
    intro x
    have hx : (x : Y) ∈ K := hle (by rw [hDB]; exact x.2)
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  obtain ⟨n, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hN1
  have hnD : (n : Y) ∈ D := hN n.2
  have h1 := hψ ⟨n, hnD⟩
  rw [hker, show (1 : N') = ⟨1, one_mem _⟩ from rfl] at h1
  have hpow : (n : Y) ^ N'.index = 1 := by
    have := congrArg Subtype.val h1.symm
    simpa using this
  obtain ⟨j, hj⟩ := hN2 n
  have hnj : (n : Y) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hord1 : orderOf (n : Y) ∣ N'.index := orderOf_dvd_of_pow_eq_one hpow
  have hord2 : orderOf (n : Y) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hnj
  have hcop : Nat.Coprime (N'.index) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.2 hodd)
  have : orderOf (n : Y) = 1 := Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left hord1) hord2
  exact hn1 (Subtype.ext (orderOf_eq_one_iff.1 this))

theorem exists_sylow_centralized {Y : Type} [Group Y] [Finite Y] {B N M : Subgroup Y}
    (hMN : M ≤ N) [hMn : (M.subgroupOf N).Normal] (PN : Sylow 2 ↥N)
    (hPN : ∀ x ∈ (PN : Subgroup ↥N), ∀ b ∈ B, (x : Y) * b = b * x) :
    ∃ Q : Sylow 2 ↥M, ∀ x ∈ (Q : Subgroup ↥M), ∀ b ∈ B, (x : Y) * b = b * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_inf_normal PN (M.subgroupOf N)
  let f : ↥(M.subgroupOf N) →* ↥M := (Subgroup.subgroupOfEquivOfLe hMN).toMonoidHom
  have hf : Function.Surjective f := (Subgroup.subgroupOfEquivOfLe hMN).surjective
  refine ⟨Sylow.mapSurjective hf Q₀, fun x hx b hb => ?_⟩
  rw [Sylow.coe_mapSurjective] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : (y : ↥N) ∈ (Q₀ : Subgroup ↥(M.subgroupOf N)).map (M.subgroupOf N).subtype :=
    ⟨y, hy, rfl⟩
  rw [hQ₀] at hy'
  exact hPN _ hy'.1 b hb

theorem centralizes_of_minimal_normal {Y : Type} [Group Y] [Finite Y] {D B N : Subgroup Y}
    (hB3 : IsPGroup 3 B) [hNn : N.Normal] (hND : N ≤ D) (hSz : SuzSections ↥D)
    (hN1 : N ≠ ⊥) (hmin : ∀ M : Subgroup Y, M.Normal → M ≤ N → M = ⊥ ∨ M = N)
    (hN2 : 2 ∣ Nat.card N) (PN : Sylow 2 ↥N)
    (hPN : ∀ x ∈ (PN : Subgroup ↥N), ∀ b ∈ B, (x : Y) * b = b * x) :
    (∀ n ∈ N, ∀ b ∈ B, n * b = b * n) ∧
      ((∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → IsPGroup 2 ↥N) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, S, hr, hSN, hSs, hconj, hSnorm, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hNn hN1 hmin
  set i₀ : Fin r := ⟨0, hr⟩ with hi₀
  have hconj_comm : ∀ i j, (∀ x ∈ S i, ∀ y ∈ S i, x * y = y * x) →
      ∀ x ∈ S j, ∀ y ∈ S j, x * y = y * x := by
    intro i j hab x hx y hy
    obtain ⟨g, hg⟩ := hconj i j
    rw [hg] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← map_mul, ← map_mul, hab x' hx' y' hy']
  have hcard : ∀ i j, Nat.card (S i) = Nat.card (S j) := by
    intro i j
    obtain ⟨g, hg⟩ := hconj i j
    rw [hg]
    exact (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).symm
  by_cases hab : ∀ x ∈ S i₀, ∀ y ∈ S i₀, x * y = y * x
  ·
    have : IsMulCommutative (S i₀) := ⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩
    let : CommGroup (S i₀) := { (inferInstance : Group (S i₀)) with
      mul_comm := fun a b => Subtype.ext (hab _ a.2 _ b.2) }
    have hp : (Nat.card (S i₀)).Prime := IsSimpleGroup.prime_card
    have hNcard : Nat.card N = Nat.card (S i₀) ^ r := by
      rw [← Nat.card_congr e.toEquiv, Nat.card_pi]
      rw [Finset.prod_congr rfl (fun i _ => hcard i i₀)]
      simp
    have hp2 : Nat.card (S i₀) = 2 := by
      rw [hNcard] at hN2
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
        (Nat.prime_two.dvd_of_dvd_pow hN2)).symm
    have hN2g : IsPGroup 2 ↥N := IsPGroup.of_card (n := r) (by rw [hNcard, hp2])
    have hPtop : (PN : Subgroup ↥N) = ⊤ :=
      (PN.is_maximal' (Q := ⊤) (hN2g.of_equiv Subgroup.topEquiv.symm) le_top).symm
    refine ⟨fun n hn b hb => ?_, fun _ => hN2g⟩
    exact hPN ⟨n, hn⟩ (by rw [hPtop]; exact Subgroup.mem_top _) b hb
  · have hnabi : ∀ i, ¬ ∀ x ∈ S i, ∀ y ∈ S i, x * y = y * x :=
      fun i h => hab (hconj_comm i i₀ h)
    refine ⟨?_, fun h => absurd (fun x hx y hy => h x (hSN i₀ hx) y (hSN i₀ hy)) hab⟩
    have hsl : ∀ i, SuzLike (S i) := by
      intro i
      have hn := hnabi i
      push Not at hn
      obtain ⟨x, hx, y, hy, hxy⟩ := hn
      have := hSs i
      exact hSz ((S i).subgroupOf D) (S i)
        (Subgroup.subgroupOfEquivOfLe ((hSN i).trans hND)).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe ((hSN i).trans hND)).surjective
        ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
    have hfac : ∀ i, ∀ b ∈ B, ∀ x ∈ S i, b * x * b⁻¹ = x := by
      intro i b hb
      have := hSs i
      have := hSnorm i
      obtain ⟨Q, hQ⟩ := exists_sylow_centralized (B := B) (hSN i) PN hPN
      have hQne : (Q : Subgroup ↥(S i)) ≠ ⊥ := by
        intro h
        have h1 := Sylow.card_eq_multiplicity Q
        rw [h, Subgroup.card_bot] at h1
        have h2 : 0 < (Nat.card (S i)).factorization 2 :=
          Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' (hsl i).1
        have : 2 ^ 1 ≤ 2 ^ (Nat.card (S i)).factorization 2 := Nat.pow_le_pow_right (by norm_num) h2
        omega
      obtain ⟨⟨x₀, hx₀Q⟩, hx₀'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQne
      have hx₀ : x₀ ≠ 1 := fun h => hx₀' (Subtype.ext h)
      have hx₀c := hQ x₀ hx₀Q
      have hnorm : ∀ b ∈ B, ∀ s ∈ S i, b * s * b⁻¹ ∈ S i := by
        intro b hb
        set S' : Subgroup Y := (S i).map (MulAut.conj b).toMonoidHom with hS'
        have hx₀S' : ((x₀ : ↥(S i)) : Y) ∈ S' := by
          refine ⟨(x₀ : Y), x₀.2, ?_⟩
          have := hx₀c b hb
          show b * (x₀ : Y) * b⁻¹ = x₀
          rw [← this]; group
        have hSN_conj : ∀ n ∈ N, ∀ h ∈ S i, n * h * n⁻¹ ∈ S i := by
          intro n hn h hh
          have := (hSnorm i).conj_mem ⟨h, hSN i hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨n, hn⟩
          exact Subgroup.mem_subgroupOf.1 this
        have hnormT : (((S i) ⊓ S').subgroupOf (S i)).Normal := by
          refine ⟨fun x hx s => ?_⟩
          rw [Subgroup.mem_subgroupOf] at hx ⊢
          refine ⟨(s * x * s⁻¹).2, ?_⟩
          obtain ⟨h, hh, hhx⟩ := hx.2
          have hsN : (b⁻¹ * (s : Y) * b) ∈ N := by
            have := hNn.conj_mem (s : Y) (hSN i s.2) b⁻¹
            simpa using this
          refine ⟨(b⁻¹ * (s : Y) * b) * h * (b⁻¹ * (s : Y) * b)⁻¹,
            hSN_conj _ hsN h hh, ?_⟩
          have hhx' : b * h * b⁻¹ = (x : Y) := by simpa [MulAut.conj_apply] using hhx
          show b * ((b⁻¹ * (s : Y) * b) * h * (b⁻¹ * (s : Y) * b)⁻¹) * b⁻¹ = (s : Y) * x * (s : Y)⁻¹
          rw [← hhx']
          group
        have := hnormT
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((S i) ⊓ S').subgroupOf (S i)) with h | h
        · exfalso
          have hmem : x₀ ∈ ((S i) ⊓ S').subgroupOf (S i) :=
            Subgroup.mem_subgroupOf.2 ⟨x₀.2, hx₀S'⟩
          rw [h, Subgroup.mem_bot] at hmem
          exact hx₀ hmem
        · have hle : S i ≤ S' := fun s hs => by
            have : (⟨s, hs⟩ : S i) ∈ ((S i) ⊓ S').subgroupOf (S i) := by rw [h]; exact Subgroup.mem_top _
            exact (Subgroup.mem_subgroupOf.1 this).2
          have heq : S i = S' := Subgroup.eq_of_le_of_card_ge hle
            (by rw [hS', Subgroup.card_map_of_injective (MulAut.conj b).injective])
          intro s hs
          have h1 : b * s * b⁻¹ ∈ S' := ⟨s, hs, rfl⟩
          rwa [← heq] at h1
      have hbn : ∀ b ∈ B, b ∈ Subgroup.normalizer (S i : Set Y) := by
        intro b hb
        rw [Subgroup.mem_normalizer_iff]
        intro h
        refine ⟨fun hh => hnorm b hb h hh, fun hh => ?_⟩
        have := hnorm b⁻¹ (B.inv_mem hb) _ hh
        simpa [mul_assoc] using this
      set α : MulAut (S i) := Subgroup.normalizerMonoidHom (S i) ⟨b, hbn b hb⟩ with hαdef
      have hα : ∀ x : S i, ((α x : S i) : Y) = b * x * b⁻¹ := fun x => rfl
      obtain ⟨k, hk⟩ := hB3 ⟨b, hb⟩
      have hαk : α ^ 3 ^ k = 1 := by
        have : (⟨b, hbn b hb⟩ : Subgroup.normalizer (S i : Set Y)) ^ 3 ^ k = 1 :=
          Subtype.ext (by simpa using congrArg Subtype.val hk)
        rw [hαdef, ← map_pow, this, map_one]
      have hfix : ∀ x ∈ (Q : Subgroup ↥(S i)), α x = x := by
        intro x hx
        apply Subtype.ext
        rw [hα]
        have := hQ x hx b hb
        rw [← this]
        group
      have hα1 := (hsl i).2 Q α hfix k hαk
      intro x hx
      have := congrArg (fun a : MulAut (S i) => ((a ⟨x, hx⟩ : S i) : Y)) hα1
      simpa [hα] using this
    intro n hn b hb
    let g₁ : (∀ i, S i) →* N := ((MulAut.conjNormal b : MulAut N).toMonoidHom).comp e.toMonoidHom
    let g₂ : (∀ i, S i) →* N := e.toMonoidHom
    have hg : g₁ = g₂ := by
      apply MonoidHom.pi_ext
      intro i x
      have hex : ((e (Pi.mulSingle i x) : N) : Y) = x := by
        rw [he i (Pi.mulSingle i x) (fun j hj => by simp [hj])]
        simp
      apply Subtype.ext
      show b * ((e (Pi.mulSingle i x) : N) : Y) * b⁻¹ = ((e (Pi.mulSingle i x) : N) : Y)
      rw [hex]
      exact hfac i b hb x x.2
    obtain ⟨y, hy⟩ := e.surjective ⟨n, hn⟩
    have h1 := congrArg (fun g : (∀ i, S i) →* N => ((g y : N) : Y)) hg
    have h2 : ((e y : N) : Y) = n := by rw [hy]
    have h3 : b * ((e y : N) : Y) * b⁻¹ = ((e y : N) : Y) := h1
    rw [h2, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm

theorem odd_card_of_centralizes_sylow :
    ∀ (n : ℕ) {Y : Type} [Group Y] [Finite Y] (D B : Subgroup Y), Nat.card D = n →
      D.Normal → IsPGroup 3 B → ¬ 3 ∣ Nat.card D → SuzSections ↥D → ⁅D, B⁆ = D →
      (∃ P : Sylow 2 ↥D, ∀ x ∈ (P : Subgroup ↥D), ∀ b ∈ B, (x : Y) * b = b * x) →
      Odd (Nat.card D) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y _ _ D B hn hDn hB3 h3 hSz hcomm ⟨P, hP⟩
  by_contra hodd
  have hev : Even (Nat.card D) := Nat.not_odd_iff_even.1 hodd
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hev
    exact absurd hev (by decide)
  obtain ⟨N, ⟨hNn, hNne, hND⟩, hNmin⟩ :=
    (Set.toFinite {M : Subgroup Y | M.Normal ∧ M ≠ ⊥ ∧ M ≤ D}).exists_minimal
      ⟨D, hDn, hDne, le_rfl⟩
  have : N.Normal := hNn
  have hmin : ∀ M : Subgroup Y, M.Normal → M ≤ N → M = ⊥ ∨ M = N := by
    intro M hM hle
    by_cases hM1 : M = ⊥
    · exact Or.inl hM1
    · exact Or.inr (le_antisymm hle (hNmin ⟨hM, hM1, hle.trans hND⟩ hle))
  set f : Y →* Y ⧸ N := QuotientGroup.mk' N with hf
  have hfs : Function.Surjective f := QuotientGroup.mk'_surjective N
  have hrel := relIndex_mul_card hND
  have hcardD' : Nat.card (D.map f) = N.relIndex D := card_map_mk_eq_relIndex D N
  have hNcard : 2 ≤ Nat.card N := by
    have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hNne
    have := Nat.card_pos (α := N)
    have h2 : 1 < Nat.card N := Finite.one_lt_card
    omega
  have hRpos : 0 < N.relIndex D := by
    rcases Nat.eq_zero_or_pos (N.relIndex D) with h | h
    · rw [h] at hrel
      have := Nat.card_pos (α := D)
      omega
    · exact h
  have hlt : Nat.card (D.map f) < n := by
    rw [hcardD', ← hn, ← hrel]
    nlinarith
  have hodd' : Odd (Nat.card (D.map f)) := by
    refine ih _ hlt (D.map f) (B.map f) rfl (hDn.map f hfs) (hB3.map f) ?_
      (hSz.of_surjective (f.subgroupMap D) (MonoidHom.subgroupMap_surjective _ _)) ?_ ?_
    · rw [hcardD']
      intro h
      exact h3 (h.trans (Dvd.intro _ hrel))
    · rw [← Subgroup.map_commutator, hcomm]
    · obtain ⟨P', hP'⟩ : ∃ P' : Sylow 2 ↥(D.map f), P' = Sylow.mapSurjective
          (MonoidHom.subgroupMap_surjective f D) P := ⟨_, rfl⟩
      refine ⟨P', fun x hx b' hb' => ?_⟩
      rw [hP', Sylow.coe_mapSurjective] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hb'
      show f (y : Y) * f b = f b * f (y : Y)
      rw [← map_mul, ← map_mul, hP y hy b hb]
  rw [hcardD'] at hodd'
  have hN2 : 2 ∣ Nat.card N := by
    have : Even (Nat.card N) := by
      rw [← hrel] at hev
      rcases Nat.even_mul.1 hev with h | h
      · exact absurd h (Nat.not_even_iff_odd.2 hodd')
      · exact h
    exact even_iff_two_dvd.1 this
  have : (N.subgroupOf D).Normal := hNn.comap D.subtype
  obtain ⟨Q, hQ⟩ := exists_sylow_centralized (B := B) (N := D) (M := N) hND P hP
  obtain ⟨hBN, hN2g⟩ := centralizes_of_minimal_normal hB3 hND hSz hNne hmin hN2 Q hQ
  have hcent := commutator_eq_bot_of_centralizes hcomm hBN
  by_cases hc : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x
  · exact false_of_central_two_group hcomm hDn hND hNne (hN2g hc) hcent hBN hodd'
  · push Not at hc
    obtain ⟨x, hx, y, hy, hxy⟩ := hc
    apply hxy
    have : ⁅x, y⁆ ∈ ⁅D, N⁆ := Subgroup.commutator_mem_commutator (hND hx) hy
    rw [hcent, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this

end CFSG.HardMathSupport.Solomon.Coordinator
