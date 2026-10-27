module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141b
public import CFSG.Yardstones.Md42047359a2a.Definitions
import CFSG.Adapters.LinearCatalogStated
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

@[expose] def Input14_1CoreSimple : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → IsChevSimple 2 S →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 →
    ∀ J : Subgroup S, GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J →
      IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) →
    ∀ k : S, k ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β → IsPGroup 2 ↥(Subgroup.zpowers k) →
      InducesInner 3 J k

@[expose] def Input14_1StructSimple : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → IsChevSimple 2 S →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 →
    ∀ J : Subgroup S, GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J →
      IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) →
    ∃ 𝓛 : Set (Subgroup S),
      (∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) ∧
      (∀ k ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β, IsPGroup 2 ↥(Subgroup.zpowers k) →
        k ∈ sSup 𝓛) ∧
      J ≤ ⨆ (L ∈ 𝓛) (_ : CFSG.Open.IsComponentOf L (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β)), L

section Family

variable {G : Type} [Group G] [Finite G]

theorem inducesInner_of_mem_family {𝓛 : Set (Subgroup G)} {J : Subgroup G} (hJ : J ∈ 𝓛)
    (hcomm : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) {k : G} (hk : k ∈ sSup 𝓛) :
    InducesInner 3 J k := by
  set M : Subgroup G := sSup (𝓛 \ {J}) with hM
  have hMC : M ≤ Subgroup.centralizer (J : Set G) := by
    refine sSup_le fun L hL => fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    exact hcomm J hJ L hL.1 (fun h => hL.2 h.symm) y hy x hx
  have hle : sSup 𝓛 ≤ J ⊔ M := by
    refine sSup_le fun L hL => ?_
    by_cases hLJ : L = J
    · rw [hLJ]
      exact le_sup_left
    · exact le_sup_of_le_right (le_sSup ⟨hL, hLJ⟩)
  have hJM : ∀ a ∈ J, ∀ c ∈ M, a * c = c * a := fun a ha c hc =>
    (Subgroup.mem_centralizer_iff.1 (hMC hc) a ha)
  obtain ⟨j, hj, m, hm, rfl⟩ := Input183.mem_sup_of_commute hJM (hle hk)
  refine ⟨j, hj, ?_⟩
  rw [inv_mul_cancel_left]
  exact Inputs141.mem_centBar_of_mem_centralizer (hMC hm)

theorem mem_of_le_iSup_components {C J : Subgroup G} {𝓛 : Set (Subgroup G)} (hJ : GLAPComponent 3 C J)
    (hle : J ≤ ⨆ (L ∈ 𝓛) (_ : CFSG.Open.IsComponentOf L C), L) : J ∈ 𝓛 := by
  have hlay : J ≤ GLALayer C := hle.trans (iSup₂_le fun L _ => iSup_le fun hL => le_sSup hL)
  obtain ⟨hJc, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ hlay
  have hJne : J ≠ ⊥ := Input183.glaPComponent_ne_bot' hJ
  have hJperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  by_contra hJL
  have hcent : ∀ L ∈ 𝓛, CFSG.Open.IsComponentOf L C → L ≤ Subgroup.centralizer (J : Set G) := by
    intro L hL hLc
    rcases CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_comp_le_or_comm hLc hJ.1 hJ.2.1 with h | h
    · rcases CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_comp_le_or_comm hJc hLc.1 hLc.2.1 with h' | h'
      · exact absurd (by rw [le_antisymm h' h]; exact hL) hJL
      · rw [Subgroup.commutator_comm] at h'
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h'
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  have hJC : J ≤ Subgroup.centralizer (J : Set G) :=
    hle.trans (iSup₂_le fun L hL => iSup_le fun hLc => hcent L hL hLc)
  have hbot : ⁅J, J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hJC
  rw [hJperf] at hbot
  exact hJne hbot

end Family

theorem input14_1CoreSimple_of_struct (h : Input14_1StructSimple) : Input14_1CoreSimple := by
  intro S _ _ hS hnc hchev β hβ3 hβ1 J hJ hJt k hk hk2
  obtain ⟨𝓛, hcomm, h2, hJle⟩ := h S hS hnc hchev β hβ3 hβ1 J hJ hJt
  exact inducesInner_of_mem_family (mem_of_le_iSup_components hJ hJle) hcomm (h2 k hk hk2)

section Transfer

theorem eq_one_of_mul_inv_mem_center {Q : Type*} [Group Q] (hQ : commutator Q = ⊤) (γ : MulAut Q)
    (h : ∀ x, γ x * x⁻¹ ∈ Subgroup.center Q) : γ = 1 := by
  let φ : Q →* ↥(Subgroup.center Q) :=
    { toFun := fun y => ⟨γ y * y⁻¹, h y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y₁ y₂ => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 (h y₂) y₁⁻¹
        show γ (y₁ * y₂) * (y₁ * y₂)⁻¹ = γ y₁ * y₁⁻¹ * (γ y₂ * y₂⁻¹)
        calc γ (y₁ * y₂) * (y₁ * y₂)⁻¹ = γ y₁ * (γ y₂ * y₂⁻¹ * y₁⁻¹) := by rw [map_mul]; group
          _ = γ y₁ * (y₁⁻¹ * (γ y₂ * y₂⁻¹)) := by rw [← hc]
          _ = γ y₁ * y₁⁻¹ * (γ y₂ * y₂⁻¹) := by group }
  have hker : commutator Q ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hQ] at hker
  ext y
  have h1 : φ y = 1 := hker (Subgroup.mem_top y)
  have h2 : γ y * y⁻¹ = 1 := congrArg Subtype.val h1
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.1 h2

theorem nonempty_quotient_center_equiv {X X' : Type} [Group X] [Group X'] (hX : CFSG.Open.IsQuasisimple X)
    (ψ : X →* X') (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center X) :
    Nonempty ((X ⧸ Subgroup.center X) ≃* (X' ⧸ Subgroup.center X')) := by
  let θ : X →* X' ⧸ Subgroup.center X' := (QuotientGroup.mk' (Subgroup.center X')).comp ψ
  have hθ : Function.Surjective θ := (QuotientGroup.mk'_surjective _).comp hψ
  have hθker : θ.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' : ψ x ∈ Subgroup.center X' := (QuotientGroup.eq_one_iff _).1 hx
      refine Inputs141.mem_center_of_commutator_mem_center hX fun y => hker ?_
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [← Subgroup.mem_center_iff.1 hx' (ψ y)]
      group
    · intro hx
      show QuotientGroup.mk' (Subgroup.center X') (ψ x) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro y'
      obtain ⟨y, rfl⟩ := hψ y'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hθker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective θ hθ)⟩

theorem mem_normalizer_of_forall_conj_mem {G : Type*} [Group G] [Finite G] {H : Subgroup G} {c : G}
    (h : ∀ x ∈ H, c * x * c⁻¹ ∈ H) : c ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj c).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj c).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective (MulAut.conj c).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : c * y * c⁻¹ = c * x * c⁻¹ := hyx
  have hxy : y = x := by simpa using hyx'
  rw [← hxy]
  exact hy

theorem isQuasisimple_native {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) : CFSG.IsQuasisimple Q :=
  ⟨⟨hQ.1⟩, hQ.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩

theorem input14_1CoreCyc_of_coreSimple (h : Input14_1CoreSimple) : Inputs141.Input14_1CoreCyc := by
  intro Y _ _ K hKq _ _ hchev b hbN hb3 hbK J hJ hJt k hk hkb hk2
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨b, hbN⟩ with hαdef
  have hαx : ∀ x : ↥K, ((α x : ↥K) : Y) = b * x * b⁻¹ := fun x => rfl
  have hα3 : α ^ 3 = 1 := by
    have e : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (K : Set Y))) ^ 3 = 1 := Subtype.ext hb3
    rw [hαdef, ← map_pow, e, map_one]
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α =
      (K ⊓ Subgroup.centralizer ({b} : Set Y)).subgroupOf K := by
    ext x
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have e : b * (x : Y) * b⁻¹ = x := by rw [← hαx, hx]
      refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc (x : Y) * b = b * x * b⁻¹ * b := by rw [e]
        _ = b * x := by group
    · rintro ⟨-, hx⟩
      have e : (x : Y) * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 hx
      apply Subtype.ext
      rw [hαx]
      calc b * (x : Y) * b⁻¹ = x * b * b⁻¹ := by rw [e]
        _ = x := by group
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  set J₀ : Subgroup ↥K := J.subgroupOf K with hJ₀def
  have hJ₀ : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α) J₀ := by
    rw [hfix]
    exact Prop126b.glaPComponent_subgroupOf hp3 inf_le_left hJ
  set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := (QuotientGroup.ker_mk' _).le
  set β : MulAut (↥K ⧸ Subgroup.center ↥K) :=
    QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) α (Subgroup.map_center_eq α) with hβdef
  have hαβ : ∀ x, π (α x) = β (π x) := fun x => rfl
  have hβn : ∀ (n : ℕ) (x : ↥K), (β ^ n) (π x) = π ((α ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ← hαβ, ih]
  have hβ3 : β ^ 3 = 1 := by
    ext z
    obtain ⟨x, rfl⟩ := hπ z
    rw [hβn, hα3]
    rfl
  have hβ1 : β ≠ 1 := by
    intro hβ
    apply hbK
    have hα1 : α = 1 := eq_one_of_mul_inv_mem_center hKq.1 α fun x => hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hαβ, hβ, MulAut.one_apply, mul_inv_cancel])
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have e1 : α ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [hα1, MulAut.one_apply]
    have e : b * y * b⁻¹ = y := by
      have := congrArg Subtype.val e1
      rw [hαx] at this
      exact this
    calc y * b = b * y * b⁻¹ * b := by rw [e]
      _ = b * y := by group
  have hSs : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKq.2
  have hSnc : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hKq
  set J' : Subgroup (↥K ⧸ Subgroup.center ↥K) := J₀.map π with hJ'def
  have hJ' : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J' :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_fixSubgroup π hker α β hαβ hπ hp3 hJ₀
  have hφ1mem : ∀ x : ↥J, π (Subgroup.inclusion hJK x) ∈ J' := fun x =>
    ⟨Subgroup.inclusion hJK x, (Subgroup.mem_subgroupOf).2 x.2, rfl⟩
  let φ1 : ↥J →* ↥J' := (π.comp (Subgroup.inclusion hJK)).codRestrict J' hφ1mem
  have hφ1 : Function.Surjective φ1 := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨(x : Y), (Subgroup.mem_subgroupOf).1 hx⟩, rfl⟩
  let φ0 : ↥J →* barOf 3 J' := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J')).comp φ1
  have hφ0 : Function.Surjective φ0 := (QuotientGroup.mk'_surjective _).comp hφ1
  have hker0 : GLAPPrimeCore 3 ↥J ≤ φ0.ker := by
    intro x hx
    have := CFSG.map_pPrimeCore_le φ1 hφ1 ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).2 this
  let ψ : barOf 3 J →* barOf 3 J' := QuotientGroup.lift (GLAPPrimeCore 3 ↥J) φ0 hker0
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ0 y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hJq : CFSG.Open.IsQuasisimple (barOf 3 J) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hJ
  have hJ'q : CFSG.Open.IsQuasisimple (barOf 3 J') :=
    CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hJ'
  have hψker : ψ.ker ≤ Subgroup.center (barOf 3 J) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups (isQuasisimple_native hJq)
      (inferInstance : ψ.ker.Normal) with h | h
    · exfalso
      have hsub : Subsingleton (barOf 3 J') := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := hψ a
        obtain ⟨y, rfl⟩ := hψ b
        have hx : x ∈ ψ.ker := h ▸ Subgroup.mem_top x
        have hy : y ∈ ψ.ker := h ▸ Subgroup.mem_top y
        rw [MonoidHom.mem_ker] at hx hy
        rw [hx, hy]
      have := hJ'q.2.toNontrivial
      obtain ⟨a, b, hab⟩ := exists_pair_ne (barOf 3 J' ⧸ Subgroup.center (barOf 3 J'))
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (congrArg _ (Subsingleton.elim a b))
    · exact h
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv hJq ψ hψ hψker
  have hJ't : IsLThreeFour (barOf 3 J' ⧸ Subgroup.center (barOf 3 J')) := Lemma1245.isLThreeFour_congr eZ hJt
  set k₀ : ↥K := ⟨k, hk⟩ with hk₀def
  have hk₀fix : k₀ ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α := by
    rw [hfix]
    exact ⟨hk, hkb⟩
  have hπk₀ : π k₀ ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β :=
    CFSG.HardMathSupport.Solomon.Coordinator.map_fixSubgroup_le π hker α β hαβ ⟨k₀, hk₀fix, rfl⟩
  have hπk₀2 : IsPGroup 2 ↥(Subgroup.zpowers (π k₀)) := by
    have h1 : IsPGroup 2 ↥((Subgroup.zpowers k).comap K.subtype) :=
      hk2.comap_of_injective K.subtype K.subtype_injective
    refine (h1.map π).to_le ?_
    rw [Subgroup.zpowers_le]
    exact ⟨k₀, Subgroup.mem_comap.2 (Subgroup.mem_zpowers k), rfl⟩
  obtain ⟨j', hj', hc'⟩ := h _ hSs hSnc hchev β hβ3 hβ1 J' hJ' hJ't (π k₀) hπk₀ hπk₀2
  obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.1 hj'
  have hj₀J : (j₀ : Y) ∈ J := Subgroup.mem_subgroupOf.1 hj₀
  set c₀ : ↥K := j₀⁻¹ * k₀ with hc₀def
  have hπc₀ : π c₀ ∈ centBar 3 ⊤ J' := by
    rw [hc₀def, map_mul, map_inv]
    exact hc'
  obtain ⟨-, hπc₀N, -⟩ := Claims1245b.mem_centBar_forall_iff.1 hπc₀
  have hconjJ₀ : ∀ x ∈ J₀, c₀ * x * c₀⁻¹ ∈ J₀ := by
    have hperf : ⁅J₀.map (MulAut.conj c₀).toMonoidHom, J₀.map (MulAut.conj c₀).toMonoidHom⁆ =
        J₀.map (MulAut.conj c₀).toMonoidHom := by
      rw [← Subgroup.map_commutator, glaPComponent_perfect hJ₀]
    have hsub : J₀.map (MulAut.conj c₀).toMonoidHom ≤ J₀ ⊔ Subgroup.center ↥K := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : π (c₀ * x * c₀⁻¹) ∈ J' := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.1 hπc₀N (π x)).1 ⟨x, hx, rfl⟩
      have h2 : c₀ * x * c₀⁻¹ ∈ J'.comap π := h1
      rw [hJ'def, Subgroup.comap_map_eq, hπdef, QuotientGroup.ker_mk'] at h2
      exact h2
    have hle := Inputs141.le_of_perfect_of_le_sup hperf hsub
      (fun a _ z hz => Subgroup.mem_center_iff.1 hz a) (fun z _ z' hz' => Subgroup.mem_center_iff.1 hz' z)
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  set c : Y := (c₀ : Y) with hcdef
  have hcN : c ∈ Subgroup.normalizer (J : Set Y) := by
    apply mem_normalizer_of_forall_conj_mem
    intro x hx
    exact Subgroup.mem_subgroupOf.1 (hconjJ₀ ⟨x, hJK hx⟩ (Subgroup.mem_subgroupOf.2 hx))
  have hγ'1 : barAut 3 J' ⟨π c₀, hπc₀N⟩ = 1 := by
    have h1 := hπc₀
    unfold centBar at h1
    obtain ⟨n, hn, hnc⟩ := (Subgroup.mem_inf.1 h1).1
    have e : n = ⟨π c₀, hπc₀N⟩ := Subtype.ext hnc
    rw [← e]
    exact hn
  have hcompat : ∀ x : barOf 3 J, ψ (barAut 3 J ⟨c, hcN⟩ x) = barAut 3 J' ⟨π c₀, hπc₀N⟩ (ψ x) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H l =>
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
      show φ0 (J.normalizerMonoidHom ⟨c, hcN⟩ l) = barAut 3 J' ⟨π c₀, hπc₀N⟩ (QuotientGroup.mk (φ1 l))
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
      show QuotientGroup.mk (φ1 (J.normalizerMonoidHom ⟨c, hcN⟩ l)) = _
      congr 1
  have hγ1 : barAut 3 J ⟨c, hcN⟩ = 1 := eq_one_of_mul_inv_mem_center hJq.1 _ fun x => hψker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcompat, hγ'1, MulAut.one_apply, mul_inv_cancel])
  have hcC : c ∈ centBar 3 ⊤ J := by
    unfold centBar
    exact Subgroup.mem_inf.2 ⟨⟨⟨c, hcN⟩, hγ1, rfl⟩, Subgroup.mem_top _⟩
  exact ⟨(j₀ : Y), hj₀J, hcC⟩

theorem input14_1CoreCyc_of_struct (h : Input14_1StructSimple) : Inputs141.Input14_1CoreCyc :=
  input14_1CoreCyc_of_coreSimple (input14_1CoreSimple_of_struct h)

end Transfer

section Tools

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

variable {Q : Type} [Group Q]

@[expose] def StructAt (β : MulAut Q) (J : Subgroup Q) : Prop :=
  ∃ 𝓛 : Set (Subgroup Q),
    (∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) ∧
    (∀ k ∈ fixSubgroup β, IsPGroup 2 ↥(Subgroup.zpowers k) → k ∈ sSup 𝓛) ∧
    J ≤ ⨆ (L ∈ 𝓛) (_ : CFSG.Open.IsComponentOf L (fixSubgroup β)), L

theorem input14_1StructSimple_iff : Input14_1StructSimple ↔
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → IsChevSimple 2 S →
      ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S, GLAPComponent 3 (fixSubgroup β) J →
        IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) → StructAt β J :=
  Iff.rfl

theorem inducesInner_of_structAt [Finite Q] {β : MulAut Q} {J : Subgroup Q}
    (hJ : GLAPComponent 3 (fixSubgroup β) J) (h : StructAt β J) {k : Q} (hk : k ∈ fixSubgroup β)
    (hk2 : IsPGroup 2 ↥(Subgroup.zpowers k)) : InducesInner 3 J k := by
  obtain ⟨𝓛, hcomm, h2, hJle⟩ := h
  exact inducesInner_of_mem_family (mem_of_le_iSup_components hJ hJle) hcomm (h2 k hk hk2)

theorem structAt_of_normal_quasisimple {β : MulAut Q} {M J : Subgroup Q} (hMC : M ≤ fixSubgroup β)
    (hMn : (M.subgroupOf (fixSubgroup β)).Normal) (hMq : CFSG.Open.IsQuasisimple ↥M)
    (h2 : ∀ k ∈ fixSubgroup β, IsPGroup 2 ↥(Subgroup.zpowers k) → k ∈ M) (hJM : J ≤ M) :
    StructAt β J := by
  have hMcomp : CFSG.Open.IsComponentOf M (fixSubgroup β) :=
    ⟨hMC, CFSG.Open.IsSubnormal.step hMC hMn (CFSG.Open.IsSubnormal.refl _), hMq⟩
  refine ⟨{M}, ?_, ?_, ?_⟩
  · intro L hL L' hL' hne
    rw [Set.mem_singleton_iff] at hL hL'
    exact absurd (hL.trans hL'.symm) hne
  · intro k hk hk2
    rw [sSup_singleton]
    exact h2 k hk hk2
  · exact hJM.trans (le_iSup₂_of_le M (Set.mem_singleton M) (le_iSup_of_le hMcomp le_rfl))

theorem structAt_of_isQuasisimple_fixSubgroup {β : MulAut Q} {J : Subgroup Q}
    (hq : CFSG.Open.IsQuasisimple ↥(fixSubgroup β)) (hJ : J ≤ fixSubgroup β) : StructAt β J := by
  refine structAt_of_normal_quasisimple le_rfl ?_ hq (fun k hk _ => hk) hJ
  rw [Subgroup.subgroupOf_self]
  infer_instance

theorem card_dvd_of_isLThreeFour {J : Subgroup Q} [Finite Q]
    (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) : 20160 ∣ Nat.card ↥J := by
  have h1 := CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour hJt
  have h2 : Nat.card (barOf 3 J) = Nat.card (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) *
      Nat.card (Subgroup.center (barOf 3 J)) := Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3 : Nat.card ↥J = Nat.card (barOf 3 J) * Nat.card (GLAPPrimeCore 3 ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [h3, h2, h1]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _

theorem lt_card_of_glaPComponent [Finite Q] {β : MulAut Q} (hβ1 : β ≠ 1) {J : Subgroup Q}
    (hJ : GLAPComponent 3 (fixSubgroup β) J)
    (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) : 20160 < Nat.card Q := by
  have hC : fixSubgroup β ≠ ⊤ := by
    intro htop
    apply hβ1
    ext x
    have hx : x ∈ fixSubgroup β := htop ▸ Subgroup.mem_top x
    exact hx
  have hdvd : 20160 ∣ Nat.card ↥(fixSubgroup β) :=
    (card_dvd_of_isLThreeFour hJt).trans (Subgroup.card_dvd_of_le hJ.1)
  have hpos : 0 < Nat.card ↥(fixSubgroup β) := Nat.card_pos
  have hle : 20160 ≤ Nat.card ↥(fixSubgroup β) := Nat.le_of_dvd hpos hdvd
  have hlt : Nat.card ↥(fixSubgroup β) < Nat.card Q := by
    have h1 : Nat.card ↥(fixSubgroup β) ≤ Nat.card Q := Subgroup.card_le_card_group _
    refine lt_of_le_of_ne h1 fun h => hC ?_
    exact Subgroup.eq_top_of_card_eq _ h
  omega

variable {Q' : Type} [Group Q']

theorem fixSubgroup_congr (e : Q ≃* Q') (β : MulAut Q) :
    fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map e.toMonoidHom := by
  ext y
  rw [mem_fixSubgroup, Subgroup.mem_map_equiv, mem_fixSubgroup]
  constructor
  · intro hy
    have hy' : e (β (e.symm y)) = y := hy
    calc β (e.symm y) = e.symm (e (β (e.symm y))) := (MulEquiv.symm_apply_apply e _).symm
      _ = e.symm y := by rw [hy']
  · intro hy
    show e (β (e.symm y)) = y
    rw [hy, MulEquiv.apply_symm_apply]

theorem map_map_symm (e : Q ≃* Q') (H : Subgroup Q) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]

theorem structAt_of_congr (e : Q ≃* Q') {β : MulAut Q} {J : Subgroup Q}
    (h : StructAt (MulAut.congr e β) (J.map e.toMonoidHom)) : StructAt β J := by
  obtain ⟨𝓛, hcomm, h2, hle⟩ := h
  have hfix := fixSubgroup_congr e β
  refine ⟨(fun L : Subgroup Q' => L.map e.symm.toMonoidHom) '' 𝓛, ?_, ?_, ?_⟩
  · rintro _ ⟨L, hL, rfl⟩ _ ⟨L', hL', rfl⟩ hne _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hLL' : L ≠ L' := fun h => hne (by rw [h])
    rw [← map_mul, ← map_mul, hcomm L hL L' hL' hLL' x hx y hy]
  · intro k hk hk2
    have hek : e k ∈ fixSubgroup (MulAut.congr e β) := by
      rw [hfix]
      exact ⟨k, hk, rfl⟩
    have hek2 : IsPGroup 2 ↥(Subgroup.zpowers (e k)) := by
      have h1 := hk2.map e.toMonoidHom
      rwa [MonoidHom.map_zpowers] at h1
    have hle' : sSup 𝓛 ≤
        (sSup ((fun L : Subgroup Q' => L.map e.symm.toMonoidHom) '' 𝓛)).comap e.symm.toMonoidHom :=
      sSup_le fun L hL => Subgroup.map_le_iff_le_comap.1 (le_sSup ⟨L, hL, rfl⟩)
    have h3 := hle' (h2 (e k) hek hek2)
    rw [Subgroup.mem_comap] at h3
    simpa using h3
  · rw [← map_map_symm e J, Subgroup.map_le_iff_le_comap]
    refine hle.trans (iSup₂_le fun L hL => iSup_le fun hLc => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_iSup₂_of_le (L.map e.symm.toMonoidHom) ⟨L, hL, rfl⟩ (le_iSup_of_le ?_ le_rfl)
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e.symm hLc
    rw [hfix] at h1
    have e1 : ((fixSubgroup β).map e.toMonoidHom).map (e.symm : Q' →* Q) = fixSubgroup β :=
      map_map_symm e _
    rw [e1] at h1
    exact h1

variable {K : Type} [Group K] [Finite K] [Finite Q]

theorem exists_two_lift (π : K →* Q) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    (hodd : Nat.Coprime 2 (Nat.card π.ker)) (α : MulAut K) (β : MulAut Q) (hαβ : ∀ x, π (α x) = β (π x))
    {x : Q} (hx : x ∈ fixSubgroup β) (hx2 : IsPGroup 2 ↥(Subgroup.zpowers x)) :
    ∃ g ∈ fixSubgroup α, IsPGroup 2 ↥(Subgroup.zpowers g) ∧ π g = x := by
  obtain ⟨n, hn⟩ := hx2 ⟨x, Subgroup.mem_zpowers x⟩
  have hxn : x ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨g₀, rfl⟩ := hπ x
  set r := Nat.card π.ker with hr
  have hg₀ker : g₀ ^ (2 ^ n) ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hxn]
  have hg₀r : (g₀ ^ (2 ^ n)) ^ r = 1 := by
    have h1 : ((⟨g₀ ^ (2 ^ n), hg₀ker⟩ : π.ker) ^ r : π.ker) = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
  have hcop : Nat.Coprime (2 ^ n) r := Nat.Coprime.pow_left n hodd
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  set g : K := g₀ ^ (v * (r : ℤ)) with hgdef
  have hπg : π g = π g₀ := by
    have e : v * (r : ℤ) = 1 - u * ((2 ^ n : ℕ) : ℤ) := by linarith
    rw [hgdef, map_zpow, e, zpow_sub, zpow_one, mul_comm u, zpow_mul, zpow_natCast, hxn, one_zpow, inv_one,
      mul_one]
  have hgn : g ^ (2 ^ n) = 1 := by
    rw [hgdef, ← zpow_natCast, ← zpow_mul]
    have e : v * (r : ℤ) * ((2 ^ n : ℕ) : ℤ) = ((2 ^ n * r : ℕ) : ℤ) * v := by push_cast; ring
    rw [e, zpow_mul, zpow_natCast, pow_mul, hg₀r, one_zpow]
  have hg2 : IsPGroup 2 ↥(Subgroup.zpowers g) := by
    rintro ⟨y, hy⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgn, one_zpow]
  refine ⟨g, ?_, hg2, hπg⟩
  set z : K := g⁻¹ * α g with hzdef
  have hzker : z ∈ π.ker := by
    have hβ : β (π g₀) = π g₀ := hx
    rw [MonoidHom.mem_ker, hzdef, map_mul, map_inv, hαβ, hπg, hβ, inv_mul_cancel]
  have hzc : z ∈ Subgroup.center K := hker hzker
  have hαg : α g = g * z := by rw [hzdef]; group
  have hzn : z ^ (2 ^ n) = 1 := by
    have h1 : (α g) ^ (2 ^ n) = 1 := by rw [← map_pow, hgn, map_one]
    have hgz : Commute g z := (Subgroup.mem_center_iff.1 hzc g)
    rw [hαg, hgz.mul_pow, hgn, one_mul] at h1
    exact h1
  have hzr : z ^ r = 1 := by
    have h1 : ((⟨z, hzker⟩ : π.ker) ^ r : π.ker) = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
  have hz1 : z = 1 := by
    have h3 : orderOf z ∣ Nat.gcd (2 ^ n) r :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzn) (orderOf_dvd_of_pow_eq_one hzr)
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  show α g = g
  rw [hαg, hz1, mul_one]

theorem isComponentOf_map_fixSubgroup (π : K →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) (α : MulAut K) (β : MulAut Q) (hαβ : ∀ x, π (α x) = β (π x))
    {L : Subgroup K} (hL : CFSG.Open.IsComponentOf L (fixSubgroup α)) :
    CFSG.Open.IsComponentOf (L.map π) (fixSubgroup β) := by
  have hmapC := CFSG.HardMathSupport.Solomon.Coordinator.map_fixSubgroup_le π hker α β hαβ
  refine ⟨(Subgroup.map_mono hL.1).trans hmapC, ?_, ?_⟩
  · have h1 : CFSG.Open.IsSubnormal (L.map π) ((fixSubgroup α).map π) := hL.2.1.map π
    have h2 : CFSG.Open.IsSubnormal ((fixSubgroup α).map π) (fixSubgroup β) :=
      CFSG.Open.IsSubnormal.step hmapC
        (CFSG.HardMathSupport.Solomon.Coordinator.normal_map_fixSubgroup π hker α β hαβ hπ)
        (CFSG.Open.IsSubnormal.refl _)
    exact h1.trans h2
  · have hne : (π.comp L.subtype).ker ≠ ⊤ := by
      intro htop
      obtain ⟨a, b, hab⟩ := CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_exists_noncomm_of_isQuasisimple hL.2.2
      apply hab
      have ha : a ∈ (π.comp L.subtype).ker := htop ▸ Subgroup.mem_top a
      have ha' : π a = 1 := ha
      have hac : (a : K) ∈ Subgroup.center K := hker (MonoidHom.mem_ker.2 ha')
      exact Subtype.ext (Subgroup.mem_center_iff.1 hac b).symm
    have hq := CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hL.2.2 (π.comp L.subtype) hne
    have hrange : L.map π = (π.comp L.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact CFSG.ComponentClassification.Components.quasisimple_of_equiv (MulEquiv.subgroupCongr hrange) hq

theorem structAt_of_cover (π : K →* Q) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    (hodd : Nat.Coprime 2 (Nat.card π.ker)) (α : MulAut K) (β : MulAut Q) (hαβ : ∀ x, π (α x) = β (π x))
    {J : Subgroup Q} (hJ : GLAPComponent 3 (fixSubgroup β) J)
    (h : ∀ J₀ : Subgroup K, GLAPComponent 3 (fixSubgroup α) J₀ → J₀.map π = J → StructAt α J₀) :
    StructAt β J := by
  obtain ⟨J₀, hJ₀, hJ₀J⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_glaPComponent_map_fixSubgroup π hker α β
    hαβ hπ Nat.prime_three hJ
  obtain ⟨𝓛, hcomm, h2, hle⟩ := h J₀ hJ₀ hJ₀J
  refine ⟨(fun L : Subgroup K => L.map π) '' 𝓛, ?_, ?_, ?_⟩
  · rintro _ ⟨L, hL, rfl⟩ _ ⟨L', hL', rfl⟩ hne _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hLL' : L ≠ L' := fun h => hne (by rw [h])
    rw [← map_mul, ← map_mul, hcomm L hL L' hL' hLL' x hx y hy]
  · intro x hx hx2
    obtain ⟨g, hg, hg2, rfl⟩ := exists_two_lift π hπ hker hodd α β hαβ hx hx2
    have hle' : sSup 𝓛 ≤ (sSup ((fun L : Subgroup K => L.map π) '' 𝓛)).comap π :=
      sSup_le fun L hL => Subgroup.map_le_iff_le_comap.1 (le_sSup ⟨L, hL, rfl⟩)
    exact hle' (h2 g hg hg2)
  · rw [← hJ₀J, Subgroup.map_le_iff_le_comap]
    refine hle.trans (iSup₂_le fun L hL => iSup_le fun hLc => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (L.map π) ⟨L, hL, rfl⟩
      (le_iSup_of_le (isComponentOf_map_fixSubgroup π hπ hker α β hαβ hLc) le_rfl)

end Tools

section Indices

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.Yardstones.Md0ec50421ce4 (ambiguousChev onLie)

@[expose] def Input14_1StructFor (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, P d.1 → d.1.characteristic = 2 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S, GLAPComponent 3 (fixSubgroup β) J →
      IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) → StructAt β J

theorem input14_1StructFor_or {P P' : TauCeti.LieTypeIndex → Prop} (h : Input14_1StructFor P)
    (h' : Input14_1StructFor P') : Input14_1StructFor fun d => P d ∨ P' d := by
  intro S _ _ hS hnc d hd
  rcases hd with hd | hd
  · exact h S hS hnc d hd
  · exact h' S hS hnc d hd

theorem input14_1StructFor_of_families
    (h : ∀ F : CFSG.Yardstones.Md42047359a2a.LieFamily,
      Input14_1StructFor fun d => CFSG.Yardstones.Md42047359a2a.lieFamily d = F) :
    Input14_1StructFor fun _ => True :=
  fun S _ _ hS hnc d _ => h _ S hS hnc d rfl

theorem card_le_of_ambiguousChev_two {S : Type} [Group S] {i : TauCeti.CFSGIndex} (hi : ambiguousChev 2 i)
    (e : S ≃* i.Group) : Nat.card S ≤ 20160 := by
  rw [Nat.card_congr e.toEquiv]
  cases i with
  | alternating n hn =>
    simp only [ambiguousChev] at hi
    have hn' : n = 5 ∨ n = 6 ∨ n = 8 := by omega
    show Nat.card (alternatingGroup (Fin n)) ≤ 20160
    rcases hn' with rfl | rfl | rfl <;>
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] <;> decide
  | lie d =>
    obtain ⟨x, hx⟩ := d
    have hi' : ambiguousChev 2 (TauCeti.CFSGIndex.lie ⟨x, hx⟩) := hi
    cases x with
    | A n q =>
      rcases n with _ | _ | n
      · simp [ambiguousChev] at hi'
      · simp only [ambiguousChev] at hi'
        have hq7 : q.card = 7 := by omega
        have hcard : q.p ^ q.exponent = 7 := by rw [← TauCeti.PrimePower.card_def]; exact hq7
        have hp : q.p = 7 := by
          have hdvd : q.p ∣ 7 := hcard ▸ dvd_pow_self q.p q.exponent_pos.ne'
          exact (Nat.prime_dvd_prime_iff_eq q.prime_p (by norm_num)).1 hdvd
        have he : q.exponent = 1 := by
          rw [hp] at hcard
          exact Nat.pow_right_injective (by norm_num : 2 ≤ 7) (show 7 ^ q.exponent = 7 ^ 1 by simpa using hcard)
        have hM := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hx (MulEquiv.refl _)
        rw [hp, he] at hM
        rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven hM]
        norm_num
      · simp [ambiguousChev] at hi'
    | twistedA n q =>
      rcases n with _ | _ | _ | n
      · simp [ambiguousChev] at hi'
      · simp [ambiguousChev] at hi'
      · simp only [ambiguousChev] at hi'
        have hq3 : q.card = 3 := hi'.1
        have hcard : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact hq3
        have hp : q.p = 3 := by
          have hdvd : q.p ∣ 3 := hcard ▸ dvd_pow_self q.p q.exponent_pos.ne'
          exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hdvd
        have he : q.exponent = 1 := by
          rw [hp] at hcard
          exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (show 3 ^ q.exponent = 3 ^ 1 by simpa using hcard)
        have hM := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hx (MulEquiv.refl _)
        rw [hp, he] at hM
        rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hM]
        norm_num
      · rcases n with _ | n <;> simp [ambiguousChev] at hi'
    | _ => simp [ambiguousChev] at hi'
  | cyclic _ _ => simp [ambiguousChev] at hi
  | sporadic _ => simp [ambiguousChev] at hi

theorem input14_1StructSimple_of_for (h : Input14_1StructFor fun _ => True) : Input14_1StructSimple := by
  intro S _ _ hS hnc hchev β hβ3 hβ1 J hJ hJt
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d => exact h S hS hnc d trivial hi ⟨e⟩ β hβ3 hβ1 J hJ hJt
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
  · exfalso
    have hlt := lt_card_of_glaPComponent hβ1 hJ hJt
    have hle := card_le_of_ambiguousChev_two hi e
    omega

theorem input14_1CoreCyc_of_for (h : Input14_1StructFor fun _ => True) : Inputs141.Input14_1CoreCyc :=
  input14_1CoreCyc_of_struct (input14_1StructSimple_of_for h)

@[expose] def Input14_1CoreFor (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, P d.1 → d.1.characteristic = 2 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S, GLAPComponent 3 (fixSubgroup β) J →
      IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) →
    ∀ k : S, k ∈ fixSubgroup β → IsPGroup 2 ↥(Subgroup.zpowers k) → InducesInner 3 J k

theorem input14_1CoreFor_of_struct {P : TauCeti.LieTypeIndex → Prop} (h : Input14_1StructFor P) :
    Input14_1CoreFor P :=
  fun S _ _ hS hnc d hd hchar he β hβ3 hβ1 J hJ hJt _ hk hk2 =>
    inducesInner_of_structAt hJ (h S hS hnc d hd hchar he β hβ3 hβ1 J hJ hJt) hk hk2

theorem input14_1CoreFor_or {P P' : TauCeti.LieTypeIndex → Prop} (h : Input14_1CoreFor P)
    (h' : Input14_1CoreFor P') : Input14_1CoreFor fun d => P d ∨ P' d := by
  intro S _ _ hS hnc d hd
  rcases hd with hd | hd
  · exact h S hS hnc d hd
  · exact h' S hS hnc d hd

theorem input14_1CoreSimple_of_coreFor (h : Input14_1CoreFor fun _ => True) : Input14_1CoreSimple := by
  intro S _ _ hS hnc hchev β hβ3 hβ1 J hJ hJt k hk hk2
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d => exact h S hS hnc d trivial hi ⟨e⟩ β hβ3 hβ1 J hJ hJt k hk hk2
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
  · exfalso
    have hlt := lt_card_of_glaPComponent hβ1 hJ hJt
    have hle := card_le_of_ambiguousChev_two hi e
    omega

theorem input14_1CoreCyc_of_coreFor (h : Input14_1CoreFor fun _ => True) : Inputs141.Input14_1CoreCyc :=
  input14_1CoreCyc_of_coreSimple (input14_1CoreSimple_of_coreFor h)

theorem input14_1CoreCyc_of_coreFamilies
    (h : ∀ F : CFSG.Yardstones.Md42047359a2a.LieFamily,
      Input14_1CoreFor fun d => CFSG.Yardstones.Md42047359a2a.lieFamily d = F) :
    Inputs141.Input14_1CoreCyc :=
  input14_1CoreCyc_of_coreFor fun S _ _ hS hnc d _ => h _ S hS hnc d rfl

theorem input14_1CoreCyc_of_families
    (h : ∀ F : CFSG.Yardstones.Md42047359a2a.LieFamily,
      Input14_1StructFor fun d => CFSG.Yardstones.Md42047359a2a.lieFamily d = F) :
    Inputs141.Input14_1CoreCyc :=
  input14_1CoreCyc_of_for (input14_1StructFor_of_families h)

end Indices

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141c

end
