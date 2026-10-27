module

public import CFSG.Goldschmidt.Steps.G310Layer
import CFSG.Goldschmidt.Steps.LemmaXBasic

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le)

section Simple

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem eq_one_of_mem_pGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R T : Subgroup X}
    (hR : IsPGroup p R) (hT : IsPGroup 2 T) {x : X} (hxR : x ∈ R) (hxT : x ∈ T) : x = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hR ⟨x, hxR⟩
  obtain ⟨m, hm⟩ := hT ⟨x, hxT⟩
  have h1 : x ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h2 : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime (p ^ n) (2 ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h3 : orderOf x ∣ Nat.gcd (p ^ n) (2 ^ m) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

theorem le_centralizer_sylowCenter [IsSimpleGroup X] {T : Sylow 2 X} {D : Subgroup X}
    (h : G3a.BorelSetup T D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup X}
    (hR : IsPGroup p R)
    (hZR : sylowCenter (T : Subgroup X) ≤ Subgroup.normalizer (R : Set X)) :
    R ≤ Subgroup.centralizer (sylowCenter (T : Subgroup X) : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := sylowCenter (T : Subgroup X) with hZ
  have hRodd : Odd (Nat.card R) := by
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hcen : ∀ u : X, u ∈ Subgroup.center X → u = 1 := by
    intro u hu
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hb | ht
    · rw [hb, Subgroup.mem_bot] at hu
      exact hu
    · exfalso
      have hTn : (T : Subgroup X).Normal := ⟨fun t htT g => by
        have hg : g ∈ Subgroup.center X := by rw [ht]; exact Subgroup.mem_top g
        rw [← Subgroup.mem_center_iff.mp hg t]
        simpa using htT⟩
      have := Sylow.unique_of_normal T hTn
      have h1 := h.card
      rw [Nat.card_unique] at h1
      have h2 := Nat.card_pos (α := (T : Subgroup X))
      omega
  refine LemmaX.le_of_forall_inf_centralizer_le (E := Z) (N := R) (J := Subgroup.centralizer
    (Z : Set X)) ⟨⟨fun a b => Subtype.ext ?_⟩⟩ h.sq h.four hZR hRodd ?_
  · exact (mem_sylowCenter.mp b.2).2 a (sylowCenter_le _ a.2)
  · intro u hu hu1 r ⟨hrR, hru⟩
    have hTC : (T : Subgroup X) ≤ Subgroup.centralizer ({u} : Set X) := by
      intro t ht
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mem_sylowCenter.mp hu).2 t ht
    have hCne : Subgroup.centralizer ({u} : Set X) ≠ ⊤ := by
      intro htop
      apply hu1
      apply hcen
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({u} : Set X) := by rw [htop]; exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    have hrN := h.le_normalizer_of_le hTC hCne hru
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzT : z ∈ (T : Subgroup X) := sylowCenter_le _ hz
    have h0 : z * r⁻¹ * z⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hZR hz) r⁻¹).mp (R.inv_mem hrR)
    have h1 : r * z * r⁻¹ * z⁻¹ ∈ R := by
      have := R.mul_mem hrR h0
      rwa [show r * (z * r⁻¹ * z⁻¹) = r * z * r⁻¹ * z⁻¹ by group] at this
    have h2 : r * z * r⁻¹ * z⁻¹ ∈ (T : Subgroup X) :=
      (T : Subgroup X).mul_mem ((Subgroup.mem_normalizer_iff.mp hrN z).mp hzT)
        ((T : Subgroup X).inv_mem hzT)
    have h3 := eq_one_of_mem_pGroup_two hp hp2 hR T.isPGroup' h1 h2
    calc z * r = (r * z * r⁻¹ * z⁻¹)⁻¹ * r * z := by group
      _ = r * z := by rw [h3, inv_one, one_mul]

end Simple

section Act

variable {M : Type*} [Group M]

theorem conj_eq_of_act {L : Subgroup M} {g ℓ : M} (hg : g ∈ Subgroup.normalizer (L : Set M))
    (hact : ∀ y ∈ L, g⁻¹ * y * g = ℓ⁻¹ * y * ℓ) : ∀ y ∈ L, g * y * g⁻¹ = ℓ * y * ℓ⁻¹ := by
  intro y hy
  have hz : g * y * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  have h1 := hact _ hz
  have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
  rw [e] at h1
  have h2 : ℓ * y * ℓ⁻¹ = ℓ * (ℓ⁻¹ * (g * y * g⁻¹) * ℓ) * ℓ⁻¹ :=
    congrArg (fun t => ℓ * t * ℓ⁻¹) h1
  rw [h2]
  group

theorem le_normalizer_of_conj_mem {Z R : Subgroup M}
    (h : ∀ z ∈ Z, ∀ r ∈ R, z * r * z⁻¹ ∈ R) : Z ≤ Subgroup.normalizer (R : Set M) := by
  intro z hz
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨h z hz r, fun hr => ?_⟩
  have := h z⁻¹ (Z.inv_mem hz) _ hr
  simpa [mul_assoc] using this

end Act

section TypeI

variable {M : Type} [Group M] [Finite M]

theorem typeI_data
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A)
    {L : Subgroup M} (hL : IsComponentOf L (normalClosureIn ⊤ A)) (hI : IsGoldTypeI L) :
    ∃ P : Sylow 2 L, ∃ D : Subgroup (L ⧸ Subgroup.center L),
      (A ⊓ L).subgroupOf L ≤ P ∧
      fusionStronglyClosed (((A ⊓ L).subgroupOf L : Subgroup L) : Set L) (P : Subgroup L) ∧
      G3a.BorelSetup (P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L))) D ∧
      ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L)) =
        sylowCenter ((P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L)) :
          Sylow 2 (L ⧸ Subgroup.center L)) : Subgroup (L ⧸ Subgroup.center L)) := by
  have hF := compFacts hO hS hL
  obtain ⟨-, hAc, T, hT, hAT, hcl, -⟩ := hF.sstar
  obtain ⟨P, hP⟩ := G3a.exists_sylow_of_fusionIsSylowIn hT
  have hAP : (A ⊓ L).subgroupOf L ≤ P := by
    rw [hP]
    exact fun x hx => hAT hx
  have hAc' : ∀ a ∈ (A ⊓ L).subgroupOf L, ∀ b ∈ (A ⊓ L).subgroupOf L, a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (mul_comm_of_isMulCommutative hAc ha hb)
  have hcl' : fusionStronglyClosed (((A ⊓ L).subgroupOf L : Subgroup L) : Set L)
      (P : Subgroup L) := by
    intro a ha g hg
    have hg' : g⁻¹ * a * g ∈ (P : Subgroup L) := hg
    rw [hP] at hg'
    exact hcl a ha g g.2 hg'
  have hAZ : ¬ (A ⊓ L).subgroupOf L ≤ Subgroup.center L := by
    intro hle
    obtain ⟨x, hx, y, hy, hxy⟩ := hF.noncentral
    have := Subgroup.mem_center_iff.mp (hle (show (⟨x, hx.2⟩ : L) ∈ (A ⊓ L).subgroupOf L
      from hx)) ⟨y, hy⟩
    exact hxy (congrArg Subtype.val this).symm
  have hQb : fusionIsBenderGroup (L ⧸ Subgroup.center L) := by
    rcases hI with ⟨n, hn, he⟩ | ⟨n, hn, he⟩ | ⟨n, hn, he⟩
    · exact Or.inl ⟨n, by omega, he⟩
    · exact Or.inr (Or.inr ⟨n, hn, he⟩)
    · exact Or.inr (Or.inl ⟨n, hn, he⟩)
  obtain ⟨D, h⟩ := G3a.exists_borelSetup hQb
    (P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L)))
  exact ⟨P, D, hAP, hcl', h, G3a.map_eq_sylowCenter hI P hAP hAc' hcl' hAZ h⟩

theorem commutator_le_centralizer_typeI
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {L : Subgroup M} (hL : IsComponentOf L (normalClosureIn ⊤ A))
    (hI : IsGoldTypeI L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup M}
    (hR : IsPGroup p R) (hRL : R ≤ Subgroup.normalizer (L : Set M))
    (hAR : A ≤ Subgroup.normalizer (R : Set M)) :
    ⁅R, A⁆ ≤ Subgroup.centralizer (L : Set M) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2
  obtain ⟨P, D, hAP, -, h, hmap⟩ := typeI_data hO hS hL hI
  set π := QuotientGroup.mk' (Subgroup.center L) with hπ
  set Zh := sylowCenter ((P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L)) :
    Sylow 2 (L ⧸ Subgroup.center L)) : Subgroup (L ⧸ Subgroup.center L)) with hZh
  have hA2 := isPGroup_two_of_isSStarIn hS
  let Rhat : Subgroup (L ⧸ Subgroup.center L) :=
    { carrier := {q | ∃ ℓ : L, π ℓ = q ∧ ∃ r ∈ R, ∀ y ∈ L, r⁻¹ * y * r = (ℓ : M)⁻¹ * y * ℓ}
      one_mem' := ⟨1, map_one π, 1, R.one_mem, fun y _ => by simp⟩
      mul_mem' := by
        rintro _ _ ⟨ℓ₁, rfl, r₁, hr₁, h₁⟩ ⟨ℓ₂, rfl, r₂, hr₂, h₂⟩
        refine ⟨ℓ₁ * ℓ₂, map_mul π _ _, r₁ * r₂, R.mul_mem hr₁ hr₂, fun y hy => ?_⟩
        have hy' : (ℓ₁ : M)⁻¹ * y * ℓ₁ ∈ L := L.mul_mem (L.mul_mem (L.inv_mem ℓ₁.2) hy) ℓ₁.2
        calc (r₁ * r₂)⁻¹ * y * (r₁ * r₂) = r₂⁻¹ * (r₁⁻¹ * y * r₁) * r₂ := by group
          _ = r₂⁻¹ * ((ℓ₁ : M)⁻¹ * y * ℓ₁) * r₂ := by rw [h₁ y hy]
          _ = (ℓ₂ : M)⁻¹ * ((ℓ₁ : M)⁻¹ * y * ℓ₁) * ℓ₂ := h₂ _ hy'
          _ = ((ℓ₁ * ℓ₂ : L) : M)⁻¹ * y * ((ℓ₁ * ℓ₂ : L) : M) := by
              simp only [Subgroup.coe_mul]
              group
      inv_mem' := by
        rintro _ ⟨ℓ, rfl, r, hr, hact⟩
        refine ⟨ℓ⁻¹, map_inv π _, r⁻¹, R.inv_mem hr, fun y hy => ?_⟩
        have := conj_eq_of_act (hRL hr) hact y hy
        simp only [inv_inv, Subgroup.coe_inv]
        exact this }
  have hRhat : IsPGroup p Rhat := by
    rintro ⟨_, ℓ, rfl, r, hr, hact⟩
    obtain ⟨n, hn⟩ := hR ⟨r, hr⟩
    have hrn : r ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have h1 := G3a.act_pow ℓ.2 hact (p ^ n) y y.2
    rw [hrn, inv_one, one_mul, mul_one] at h1
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow]
    calc (y : M) * (ℓ : M) ^ p ^ n
        = (ℓ : M) ^ p ^ n * (((ℓ : M) ^ p ^ n)⁻¹ * y * (ℓ : M) ^ p ^ n) := by group
      _ = (ℓ : M) ^ p ^ n * y := by rw [← h1]
  have hZhR : Zh ≤ Subgroup.normalizer (Rhat : Set (L ⧸ Subgroup.center L)) := by
    apply le_normalizer_of_conj_mem
    intro z hz q hq
    rw [← hmap] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨ℓ, rfl, r, hr, hact⟩ := hq
    have hxA : (x : M) ∈ A := hx.1
    have hxN : (x : M) ∈ Subgroup.normalizer (L : Set M) := Subgroup.le_normalizer x.2
    refine ⟨x * ℓ * x⁻¹, by simp [π], (x : M) * r * (x : M)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hAR hxA) r).mp hr, fun y hy => ?_⟩
    have hy' : (x : M)⁻¹ * y * x ∈ L := L.mul_mem (L.mul_mem (L.inv_mem x.2) hy) x.2
    have h1 := hact _ hy'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc ((x : M) * r * (x : M)⁻¹)⁻¹ * y * ((x : M) * r * (x : M)⁻¹)
        = (x : M) * (r⁻¹ * ((x : M)⁻¹ * y * x) * r) * (x : M)⁻¹ := by group
      _ = (x : M) * ((ℓ : M)⁻¹ * ((x : M)⁻¹ * y * x) * ℓ) * (x : M)⁻¹ := by rw [h1]
      _ = ((x : M) * ℓ * (x : M)⁻¹)⁻¹ * y * ((x : M) * ℓ * (x : M)⁻¹) := by group
  have hBender := le_centralizer_sylowCenter h hp hp2 hRhat hZhR
  set R₀ := R ⊓ G3a.actsBy L L le_rfl with hR₀
  have hstep1 : ⁅R, A⁆ ≤ R₀ := by
    rw [Subgroup.commutator_le]
    intro r hr a ha
    obtain ⟨x, hx, hxact⟩ := exists_act_of_mem_A hO hS hL ha
    have haN : a ∈ Subgroup.normalizer (L : Set M) :=
      mem_normalizer_of_mem hO hS hL (le_normalClosureIn_top A ha)
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      have h1 : a * r⁻¹ * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hAR ha) r⁻¹).mp (R.inv_mem hr)
      have := R.mul_mem hr h1
      rwa [show r * (a * r⁻¹ * a⁻¹) = r * a * r⁻¹ * a⁻¹ by group] at this
    · rw [commutatorElement_def]
      have hrax : r * x * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hRL hr) x).mp hx.2
      refine (G3a.actsBy L L le_rfl).mul_mem (G3a.mem_actsBy.mpr ⟨r * x * r⁻¹, hrax,
        fun y hy => ?_⟩) ((G3a.actsBy L L le_rfl).inv_mem (G3a.mem_actsBy.mpr ⟨x, hx.2, hxact⟩))
      have hy' : r⁻¹ * y * r ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hRL hr)) y).mp hy
        simpa using this
      calc (r * a * r⁻¹)⁻¹ * y * (r * a * r⁻¹) = r * (a⁻¹ * (r⁻¹ * y * r) * a) * r⁻¹ := by
            group
        _ = r * (x⁻¹ * (r⁻¹ * y * r) * x) * r⁻¹ := by rw [hxact _ hy']
        _ = (r * x * r⁻¹)⁻¹ * y * (r * x * r⁻¹) := by group
  have hstep2 : ⁅R₀, A⁆ ≤ Subgroup.centralizer (L : Set M) := by
    rw [Subgroup.commutator_le]
    intro r hr a ha
    obtain ⟨ℓ, hℓ, hact⟩ := G3a.mem_actsBy.mp hr.2
    obtain ⟨x, hx, hxact⟩ := exists_act_of_mem_A hO hS hL ha
    have haN : a ∈ Subgroup.normalizer (L : Set M) :=
      mem_normalizer_of_mem hO hS hL (le_normalClosureIn_top A ha)
    have hℓR : π ⟨ℓ, hℓ⟩ ∈ Rhat := ⟨⟨ℓ, hℓ⟩, rfl, r, hr.1, hact⟩
    have hxZ : π ⟨x, hx.2⟩ ∈ Zh := by
      rw [← hmap]
      exact ⟨⟨x, hx.2⟩, hx, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp (hBender hℓR) _ hxZ
    have hu : (⟨ℓ, hℓ⟩ : L) * ⟨x, hx.2⟩ * (⟨ℓ, hℓ⟩ : L)⁻¹ * (⟨x, hx.2⟩ : L)⁻¹ ∈
        Subgroup.center L := by
      rw [← QuotientGroup.eq_one_iff (N := Subgroup.center L)]
      have : (π ⟨x, hx.2⟩) * (π ⟨ℓ, hℓ⟩) = (π ⟨ℓ, hℓ⟩) * (π ⟨x, hx.2⟩) := hc
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change π _ * π _ * (π _)⁻¹ * (π _)⁻¹ = 1
      rw [← this]
      group
    set u : L := (⟨ℓ, hℓ⟩ : L) * ⟨x, hx.2⟩ * (⟨ℓ, hℓ⟩ : L)⁻¹ * (⟨x, hx.2⟩ : L)⁻¹ with hudef
    have hucen : ∀ y ∈ L, (u : M) * y = y * u := fun y hy =>
      congrArg Subtype.val ((Subgroup.mem_center_iff.mp hu ⟨y, hy⟩).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hrN : r ∈ Subgroup.normalizer (L : Set M) := hRL hr.1
    have hact' := conj_eq_of_act hrN hact
    have hxact' := conj_eq_of_act haN hxact
    have hy1 : r⁻¹ * y * r ∈ L := by
      rw [hact y hy]
      exact L.mul_mem (L.mul_mem (L.inv_mem hℓ) hy) hℓ
    have hy2 : a⁻¹ * (r⁻¹ * y * r) * a ∈ L := by
      rw [hxact _ hy1]
      exact L.mul_mem (L.mul_mem (L.inv_mem hx.2) hy1) hx.2
    have hy3 : r * (a⁻¹ * (r⁻¹ * y * r) * a) * r⁻¹ ∈ L := by
      rw [hact' _ hy2]
      exact L.mul_mem (L.mul_mem hℓ hy2) (L.inv_mem hℓ)
    have key : (r * a * r⁻¹ * a⁻¹)⁻¹ * y * (r * a * r⁻¹ * a⁻¹) = y := by
      calc (r * a * r⁻¹ * a⁻¹)⁻¹ * y * (r * a * r⁻¹ * a⁻¹)
          = a * (r * (a⁻¹ * (r⁻¹ * y * r) * a) * r⁻¹) * a⁻¹ := by group
        _ = x * (ℓ * (x⁻¹ * (ℓ⁻¹ * y * ℓ) * x) * ℓ⁻¹) * x⁻¹ := by
            rw [hxact' _ hy3, hact' _ hy2, hxact _ hy1, hact y hy]
        _ = (u : M)⁻¹ * y * u := by
            simp only [hudef, Subgroup.coe_mul, Subgroup.coe_inv]
            group
        _ = y := by
            rw [mul_assoc, ← hucen y hy]
            group
    rw [commutatorElement_def]
    calc y * (r * a * r⁻¹ * a⁻¹)
        = (r * a * r⁻¹ * a⁻¹) * ((r * a * r⁻¹ * a⁻¹)⁻¹ * y * (r * a * r⁻¹ * a⁻¹)) := by group
      _ = (r * a * r⁻¹ * a⁻¹) * y := by rw [key]
  have hcop : Nat.Coprime (Nat.card A) (Nat.card R) := by
    obtain ⟨m, hm⟩ := hA2.exists_card_eq
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    rw [hm, hn]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  calc ⁅R, A⁆ ≤ ⁅⁅R, A⁆, A⁆ := CFSG.Walter.commutator_le_commutator_commutator R A hAR hcop
    _ ≤ ⁅R₀, A⁆ := Subgroup.commutator_mono hstep1 le_rfl
    _ ≤ Subgroup.centralizer (L : Set M) := hstep2

end TypeI

end CFSG.Goldschmidt.G310
