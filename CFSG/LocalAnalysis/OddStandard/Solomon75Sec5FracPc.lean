module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracPiece
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Cor43Perm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneSmall

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin
open scoped commutatorElement

namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem CoverSetup.mem_fixedCompOf_of_mem_center (C : CoverSetup n K) (hn : 8 ≤ n)
    {α : MulAut K} {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) (hm : 5 ≤ n - 2 * k) {x : K} (hx : x ∈ center K)
    (hx1 : x ≠ 1) : x ∈ C.fixedCompOf σ := by
  obtain ⟨-, hdc, hmap⟩ := h.fixedCompOf_isDoubleCover C hn hσ hk hm
  set L : Subgroup K := C.fixedCompOf σ with hL
  obtain ⟨z, hz1, -⟩ := (Nat.card_eq_two_iff' (1 : center ↥L)).1 hdc.2.1
  set c : K := ((z : ↥L) : K) with hc
  have hcmem : c ∈ L := (z : ↥L).2
  have hρc : C.ρ c ∈ altFixOf σ := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hcmem
  have hcomm : ∀ t ∈ altFixOf σ, t * C.ρ c = C.ρ c * t := by
    intro t ht
    rw [← hmap] at ht
    obtain ⟨l, hl, rfl⟩ := ht
    have := Subgroup.mem_center_iff.1 z.2 ⟨l, hl⟩
    have h2 := congrArg (fun y : ↥L => C.ρ (y : K)) this
    simpa [map_mul] using h2
  have hm4 : 4 ≤ (σ.support)ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, hk]
    omega
  have hρ1 : C.ρ c = 1 := eq_one_of_forall_comm_altFixOf hm4 hρc hcomm
  have hcK : c ∈ center K := (C.ρ_eq_one_iff).1 hρ1
  have hc1 : c ≠ 1 := by
    intro h1
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  rw [C.center_eq_of_ne_one hx hcK hx1 hc1]
  exact hcmem

theorem CoverSetup.mem_normalizer_fixedCompOf [Finite K] (C : CoverSetup n K) (hn : 8 ≤ n)
    {α : MulAut K} {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ}
    (hk : σ.support.card = 2 * k) (hm : 5 ≤ n - 2 * k) {y : K} (hy : y ∈ fixSub α) :
    y ∈ normalizer (C.fixedCompOf σ : Set K) := by
  have hlay := h.layer_fixSub_map_eq_of C hn hσ hk hm
  have hle : C.fixedCompOf σ ≤ fixSub α := (h.fixedCompOf_isDoubleCover C hn hσ hk hm).1
  have hnorm : ((C.fixedCompOf σ).subgroupOf (fixSub α)).Normal := by
    rw [← hlay, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (fixSub α).subtype_injective]
    have : (layer ↥(fixSub α)).Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hnorm hy

end AhatData

section Piece

variable {X : Type} [Group X] [Finite X] {n : ℕ}

theorem AhatModel.finite_K {A : Subgroup X} (M : AhatModel X n A) : Finite M.K :=
  Finite.of_equiv _ M.e.toEquiv

theorem exists_piece_of_model {Lu : Subgroup X} (M : AhatModel X n Lu) (hn : 8 ≤ n) {s : X}
    (hs : s ∈ normalizer (Lu : Set X)) (hs2 : s * s = 1)
    (h5 : 5 ≤ fixCount (M.perm s hs)) :
    ∃ P : Subgroup X, P ≤ Lu ⊓ centralizer ({s} : Set X) ∧
      (P.subgroupOf (Lu ⊓ centralizer ({s} : Set X))).Normal ∧ IsTwoGenQuasi ↥P ∧
      ∀ x ∈ Lu ⊓ centralizer ({s} : Set X), x * x = 1 → x ∉ oddCoreOf Lu →
        (∀ l ∈ Lu, ⁅l, x⁆ ∈ oddCoreOf Lu) → x ∈ P := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite M.K := M.finite_K
  set Lc : Subgroup X := Lu ⊓ centralizer ({s} : Set X) with hLc
  set σ : Perm (Fin n) := M.perm s hs with hσdef
  have hσ2 : σ * σ = 1 := by
    have key : ∀ (c : X) (hc : c ∈ normalizer (Lu : Set X)), c = 1 → M.perm c hc = 1 := by
      rintro c hc rfl
      exact M.perm_one hn
    rw [hσdef, ← M.perm_mul hn hs hs]
    exact key _ _ hs2
  obtain ⟨k, hk⟩ := exists_support_card_of_mul_self hσ2
  have hm : 5 ≤ n - 2 * k := by
    have := fixCount_add_support σ
    omega
  have hind : M.C.Induces (M.autOf s hs) σ := M.induces_perm hn s hs
  let θ : ↥Lc →* M.K :=
    (M.e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥Lu))).comp
      (Subgroup.inclusion (inf_le_left : Lc ≤ Lu))
  have hθ : ∀ g : ↥Lc, θ g = M.e (QuotientGroup.mk (⟨g.1, g.2.1⟩ : ↥Lu)) := fun g => rfl
  have hker : ¬ 2 ∣ Nat.card θ.ker := by
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥Lu)) := pPrimeCore_coprime_card
    let f : θ.ker →* pPrimeCore 2 ↥Lu :=
      { toFun := fun g => ⟨⟨g.1.1, g.1.2.1⟩, by
          have h1 : θ g.1 = 1 := g.2
          rw [hθ] at h1
          exact (QuotientGroup.eq_one_iff _).1 (M.e.injective (h1.trans (map_one M.e).symm))⟩
        map_one' := rfl
        map_mul' := fun a b => rfl }
    have hf : Function.Injective f := by
      intro a b hab
      have := congrArg (fun y : pPrimeCore 2 ↥Lu => ((y : ↥Lu) : X)) hab
      exact Subtype.ext (Subtype.ext this)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective f hf) hcop)
  obtain ⟨hLKfix, hLKdc, hLKmap⟩ := hind.fixedCompOf_isDoubleCover M.C hn hσ2 hk hm
  set LK : Subgroup M.K := M.C.fixedCompOf σ with hLK
  have hθfix : ∀ g : ↥Lc, θ g ∈ AhatData.fixSub (M.autOf s hs) := by
    intro g
    show M.autOf s hs (θ g) = θ g
    rw [hθ, M.autOf_mk]
    congr 2
    apply Subtype.ext
    rw [coe_conjAut]
    have hg := Subgroup.mem_centralizer_singleton_iff.1 g.2.2
    show s * g.1 * s⁻¹ = g.1
    rw [← hg]
    group
  have hnormK : ∀ g : ↥Lc, θ g ∈ normalizer (LK : Set M.K) := fun g =>
    M.C.mem_normalizer_fixedCompOf hn hind hσ2 hk hm (hθfix g)
  have hsurj : ∀ l ∈ LK, ∃ g : ↥Lc, θ g = l := by
    intro l hl
    obtain ⟨a, ha⟩ := M.surj_mk l
    have hlfix : M.autOf s hs l = l := hLKfix hl
    have h1 : M.e (QuotientGroup.mk (conjAut hs a)) = M.e (QuotientGroup.mk a) := by
      rw [← M.autOf_mk hs a, ha, hlfix]
    have h3 : (a⁻¹ * conjAut hs a : ↥Lu) ∈ pPrimeCore 2 ↥Lu :=
      (QuotientGroup.eq (a := a) (b := conjAut hs a)).1 (M.e.injective h1).symm
    have h4 : ((a⁻¹ * conjAut hs a : ↥Lu) : X) ∈ oddCoreOf Lu :=
      mem_oddCoreOf_iff.2 ⟨(a⁻¹ * conjAut hs a).2, h3⟩
    have e1 : ((a⁻¹ * conjAut hs a : ↥Lu) : X) = (a : X)⁻¹ * (s * (a : X) * s⁻¹) := by
      simp [coe_conjAut]
    rw [e1] at h4
    obtain ⟨p, hp, hpc⟩ := exists_mul_mem_centralizer_of_fixes_coset (P := oddCoreOf Lu)
      (odd_card_oddCoreOf Lu) (a := s) (k := 1) (by simpa [pow_two] using hs2)
      (mem_normalizer_oddCoreOf_of_mem_normalizer hs) (y := (a : X)) h4
    have hpL : p ∈ Lu := oddCoreOf_le Lu hp
    refine ⟨⟨(a : X) * p, Lu.mul_mem a.2 hpL, hpc⟩, ?_⟩
    have hpO : (⟨p, hpL⟩ : ↥Lu) ∈ pPrimeCore 2 ↥Lu := (mem_oddCoreOf_iff.1 hp).2
    rw [hθ]
    show M.e (QuotientGroup.mk (a * (⟨p, hpL⟩ : ↥Lu))) = l
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hpO, mul_one, ha]
  obtain ⟨-, hPG, -, -, hPq, -⟩ := exists_piece_abstract θ hker hm hLKdc hnormK hsurj
  set Pc : Subgroup ↥Lc := oTwoPrimeOf (LK.comap θ) with hPc
  refine ⟨Pc.map Lc.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Lc.subtype_injective]
    exact hPG
  · exact (isTwoGenQuasi_congr_iff
      (Subgroup.equivMapOfInjective Pc Lc.subtype Lc.subtype_injective)).1 hPq
  · intro x hx hx2 hxO hxc
    set xg : ↥Lc := ⟨x, hx⟩ with hxg
    have hxcen : θ xg ∈ center M.K := by
      rw [Subgroup.mem_center_iff]
      intro k
      obtain ⟨l, rfl⟩ := M.surj_mk k
      rw [hθ, ← map_mul, ← map_mul]
      congr 1
      have hmem : ⁅(l : X), x⁆ ∈ oddCoreOf Lu := hxc l l.2
      have h2 : (⁅l, (⟨x, hx.1⟩ : ↥Lu)⁆ : ↥Lu) ∈ pPrimeCore 2 ↥Lu := (mem_oddCoreOf_iff.1 hmem).2
      have h3 : (QuotientGroup.mk' (pPrimeCore 2 ↥Lu)) ⁅l, (⟨x, hx.1⟩ : ↥Lu)⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).2 h2
      rw [map_commutatorElement] at h3
      exact commutatorElement_eq_one_iff_mul_comm.1 h3
    have hθ1 : θ xg ≠ 1 := by
      intro h1
      apply hxO
      rw [hθ] at h1
      have h2 := (QuotientGroup.eq_one_iff _).1 (M.e.injective (h1.trans (map_one M.e).symm))
      exact mem_oddCoreOf_iff.2 ⟨hx.1, h2⟩
    have hLKmem : θ xg ∈ LK := M.C.mem_fixedCompOf_of_mem_center hn hind hσ2 hk hm hxcen hθ1
    have hxP : xg ∈ Pc := mem_oTwoPrimeOf (show xg ∈ LK.comap θ from hLKmem) 1
      (by apply Subtype.ext; simpa [pow_two, hxg] using hx2)
    exact ⟨xg, hxP, rfl⟩

end Piece

end CFSG.OddStandard.Solomon75
