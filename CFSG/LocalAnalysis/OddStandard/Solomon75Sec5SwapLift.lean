module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapComm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapDiag

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.LocalCores
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement


theorem map_centralizer_pPrimeCore_of_involution {D : Type} [Group D] [Finite D] {u : D}
    (hu : u * u = 1) :
    (centralizer ({u} : Set D)).map (QuotientGroup.mk' (pPrimeCore 2 D)) =
      centralizer ({(QuotientGroup.mk u : D ⧸ pPrimeCore 2 D)} : Set (D ⧸ pPrimeCore 2 D)) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : u ^ 2 = 1 := by rw [pow_two]; exact hu
  have hT : IsPGroup 2 ↥(Subgroup.zpowers u) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (by simpa using orderOf_dvd_of_pow_eq_one hu2 : orderOf u ∣ 2 ^ 1)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have : Fact (IsPGroup 2 ↥(Subgroup.zpowers u)) := ⟨hT⟩
  have h := centralizer_map_quotient_eq_map_centralizer 2 (Subgroup.zpowers u) (pPrimeCore 2 D)
    pPrimeCore_normal pPrimeCore_coprime_card
  simp only at h
  rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, Set.image_singleton] at h
  simp only [Subgroup.centralizer_closure] at h
  exact h.symm

theorem isPComponent_two_of_isQuasisimple_of_subnormal {W : Type*} [Group W] [Finite W]
    {Zb Q : Subgroup W} (hQ : IsQuasisimple ↥Q) (hQZ : Q ≤ Zb)
    (hs : (Q.subgroupOf Zb).IsSubnormal) : IsPComponent 2 (Q.subgroupOf Zb) := by
  have hcomp : IsComponent (Q.subgroupOf Zb) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQZ).symm hQ, hs⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥Zb)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥Zb))
  exact LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hcomp
    (LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hcomp
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd))

theorem exists_isPComponent_lift_of_map_eq {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (q : G →* H) (hker : ¬ 2 ∣ Nat.card q.ker) {Z : Subgroup G} {Zb M : Subgroup H}
    (hZ : Z.map q = Zb) (hMZ : M ≤ Zb) (hM : IsPComponent 2 (M.subgroupOf Zb)) :
    ∃ Δ : Subgroup G, Δ ≤ Z ∧ IsPComponent 2 (Δ.subgroupOf Z) ∧ Δ.map q = M ∧
      ∀ c ∈ Z, q c ∈ normalizer (M : Set H) → c ∈ normalizer (Δ : Set G) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥Z →* ↥Zb := (q.comp Z.subtype).codRestrict Zb
    (fun z => by rw [← hZ]; exact Subgroup.mem_map_of_mem q z.2)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hZ ▸ hy)
    exact ⟨⟨x, hx⟩, rfl⟩
  have hfker : ¬ 2 ∣ Nat.card f.ker := by
    have : f.ker = (q.domRestrict Z).ker := MonoidHom.ker_codRestrict _ _ _
    rw [this]
    exact ComponentClassification.GSThmB.OddQuot.not_two_dvd_card_ker_domRestrict q hker Z
  obtain ⟨-, hlift, -⟩ :=
    ComponentClassification.CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
      f hf hfker
  obtain ⟨hΔ₀, hΔ₀map⟩ := hlift _ hM
  set Δ₀ : Subgroup ↥Z := Subgroup.closure {x : ↥Z |
    x ∈ (M.subgroupOf Zb).comap f ∧ ∃ k : ℕ, orderOf x = 2 ^ k} with hΔ₀def
  have hsub : (Δ₀.map Z.subtype).subgroupOf Z = Δ₀ :=
    Subgroup.comap_map_eq_self_of_injective Z.subtype_injective Δ₀
  refine ⟨Δ₀.map Z.subtype, Subgroup.map_subtype_le Δ₀, ?_, ?_, ?_⟩
  · rw [hsub]
    exact hΔ₀
  · rw [Subgroup.map_map]
    have hcomp : q.comp Z.subtype = Zb.subtype.comp f := rfl
    rw [hcomp, ← Subgroup.map_map, hΔ₀map, Subgroup.map_subgroupOf_eq_of_le hMZ]
  · have hgen : ∀ c ∈ Z, q c ∈ normalizer (M : Set H) →
        ∀ y ∈ Δ₀.map Z.subtype, c * y * c⁻¹ ∈ Δ₀.map Z.subtype := by
      intro c hc hqc y hy
      obtain ⟨y', hy', rfl⟩ := hy
      have hle : Δ₀ ≤ Δ₀.comap (MulAut.conj (⟨c, hc⟩ : ↥Z)).toMonoidHom := by
        refine (Subgroup.closure_le _).2 ?_
        rintro x ⟨hxM, k, hk⟩
        show (MulAut.conj (⟨c, hc⟩ : ↥Z)) x ∈ Δ₀
        refine Subgroup.subset_closure ⟨?_, k, ?_⟩
        · have hxM' : q (x : G) ∈ M := hxM
          show q (c * (x : G) * c⁻¹) ∈ M
          rw [map_mul, map_mul, map_inv]
          exact (Subgroup.mem_normalizer_iff.1 hqc _).1 hxM'
        · exact (orderOf_injective (MulAut.conj (⟨c, hc⟩ : ↥Z)).toMonoidHom
            (MulAut.conj (⟨c, hc⟩ : ↥Z)).injective x).trans hk
      exact ⟨_, Subgroup.mem_comap.1 (hle hy'), rfl⟩
    intro c hc hqc
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hgen c hc hqc y, fun hy => ?_⟩
    have := hgen c⁻¹ (Z.inv_mem hc) (by rw [map_inv]; exact inv_mem hqc) _ hy
    simpa [mul_assoc] using this

theorem exists_isPComponent_lift {C : Type} [Group C] [Finite C] {t : C} (ht : t * t = 1)
    {Q : Subgroup (C ⧸ pPrimeCore 2 C)} (hQ : IsQuasisimple ↥Q)
    (hQC : Q ≤ centralizer ({(QuotientGroup.mk t : C ⧸ pPrimeCore 2 C)} : Set (C ⧸ pPrimeCore 2 C)))
    (hQs : (Q.subgroupOf
      (centralizer ({(QuotientGroup.mk t : C ⧸ pPrimeCore 2 C)} :
        Set (C ⧸ pPrimeCore 2 C)))).IsSubnormal) :
    ∃ Δ : Subgroup C, Δ ≤ centralizer ({t} : Set C) ∧
      IsPComponent 2 (Δ.subgroupOf (centralizer ({t} : Set C))) ∧
      Δ.map (QuotientGroup.mk' (pPrimeCore 2 C)) = Q ∧
      ∀ c ∈ centralizer ({t} : Set C), (QuotientGroup.mk c : C ⧸ pPrimeCore 2 C) ∈
        normalizer (Q : Set (C ⧸ pPrimeCore 2 C)) → c ∈ normalizer (Δ : Set C) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 C)).ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card
  exact exists_isPComponent_lift_of_map_eq (QuotientGroup.mk' (pPrimeCore 2 C)) hker
    (map_centralizer_pPrimeCore_of_involution ht) hQC
    (isPComponent_two_of_isQuasisimple_of_subnormal hQ hQC hQs)




theorem exists_mulEquiv_quot_image {C : Type} [Group C] [Finite C] {B : Subgroup C}
    (hB : IsPComponent 2 B) :
    Nonempty (↥B ⧸ pPrimeCore 2 ↥B ≃* ↥(B.map (QuotientGroup.mk' (pPrimeCore 2 C)))) := by
  obtain ⟨-, -, hsub, -, -⟩ := id hB
  exact ⟨ComponentClassification.Sp4Rec.quotientEquivMap hsub⟩




theorem commutatorElement_mul_central_aux {G : Type*} [Group G] (a b z₁ z₂ : G)
    (hz₁ : z₁ ∈ center G) (hz₂ : z₂ ∈ center G) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  have h1 : ∀ g : G, g * z₁ = z₁ * g := Subgroup.mem_center_iff.1 hz₁
  have h2 : ∀ g : G, g * z₂ = z₂ * g := Subgroup.mem_center_iff.1 hz₂
  have e1 : z₁ * (b * z₂) * z₁⁻¹ = b * z₂ := by
    rw [← h1 (b * z₂), mul_inv_cancel_right]
  have e2 : z₂ * a⁻¹ * z₂⁻¹ = a⁻¹ := by
    rw [← h2 a⁻¹, mul_inv_cancel_right]
  calc ⁅a * z₁, b * z₂⁆ = a * (z₁ * (b * z₂) * z₁⁻¹) * a⁻¹ * (z₂⁻¹ * b⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
    _ = a * b * (z₂ * a⁻¹ * z₂⁻¹) * b⁻¹ := by
        rw [e1]; simp only [mul_assoc]
    _ = ⁅a, b⁆ := by rw [e2]; simp [commutatorElement_def]

theorem center_ne_top_of_isQuasisimple_aux {Q : Type*} [Group Q] (hq : IsQuasisimple Q) :
    center Q ≠ ⊤ := by
  intro htop
  obtain ⟨a, b, hab⟩ := hq.2.2
  refine hab ?_
  refine QuotientGroup.induction_on a (fun x => ?_)
  refine QuotientGroup.induction_on b (fun y => ?_)
  have hx : x ∈ center Q := htop ▸ Subgroup.mem_top x
  have hxy : y * x = x * y := Subgroup.mem_center_iff.1 hx y
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]

theorem isPGroup_center_of_surjective {Q Q' : Type*} [Group Q] [Group Q'] [Finite Q] [Finite Q']
    (hq : IsQuasisimple Q) (hq' : IsQuasisimple Q') (hZ : IsPGroup 2 ↥(center Q))
    (φ : Q →* Q') (hφ : Function.Surjective φ) : IsPGroup 2 ↥(center Q') := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : Subgroup Q, N = (center Q').comap φ := ⟨_, rfl⟩
  have hNn : N.Normal := hN ▸ Subgroup.Normal.comap inferInstance φ
  have hmap : N.map φ = center Q' := by
    rw [hN]; exact Subgroup.map_comap_eq_self_of_surjective hφ _
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Q →* Q ⧸ center Q, ψ = QuotientGroup.mk' (center Q) := ⟨_, rfl⟩
  have hψs : Function.Surjective ψ := hψ ▸ QuotientGroup.mk'_surjective _
  have hsimple : IsSimpleGroup (Q ⧸ center Q) := hq.2.1
  have hNψ : (N.map ψ).Normal := hNn.map ψ hψs
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map ψ) with h | h
  ·
    have hNle : N ≤ center Q := by
      intro x hx
      have hx' : ψ x ∈ N.map ψ := Subgroup.mem_map_of_mem ψ hx
      rw [h, Subgroup.mem_bot, hψ] at hx'
      exact (QuotientGroup.eq_one_iff x).1 hx'
    have hle : center Q' ≤ (center Q).map φ := hmap ▸ Subgroup.map_mono hNle
    exact (hZ.map φ).to_le hle
  ·
    exfalso
    refine center_ne_top_of_isQuasisimple_aux hq' ?_
    have hdecomp : ∀ q : Q, ∃ n ∈ N, ∃ z ∈ center Q, q = n * z := by
      intro q
      have hq1 : ψ q ∈ N.map ψ := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnq⟩ := hq1
      refine ⟨n, hn, n⁻¹ * q, ?_, by simp⟩
      rw [hψ] at hnq
      exact QuotientGroup.eq.1 hnq
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdecomp g₁
      obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdecomp g₂
      rw [commutatorElement_mul_central_aux n₁ n₂ z₁ z₂ hz₁ hz₂, commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)
    have hNtop : N = ⊤ := by
      rw [eq_top_iff]
      exact le_of_eq_of_le hq.1.commutator_eq_top.symm hcomm
    rw [← hmap, hNtop, Subgroup.map_top]
    exact MonoidHom.range_eq_top.2 hφ


section DiagStep

theorem eq_of_map_pPrimeCore_eq {C : Type} [Group C] [Finite C] {A A' : Subgroup C}
    (hA : IsPComponent 2 A) (hA' : IsPComponent 2 A')
    (h : A.map (QuotientGroup.mk' (pPrimeCore 2 C)) =
      A'.map (QuotientGroup.mk' (pPrimeCore 2 C))) : A = A' := by
  have hle : ∀ {P P' : Subgroup C}, IsPComponent 2 P → IsPComponent 2 P' →
      P.map (QuotientGroup.mk' (pPrimeCore 2 C)) = P'.map (QuotientGroup.mk' (pPrimeCore 2 C)) →
      P ≤ P' := by
    intro P P' hP hP' hPP'
    have hgen : primeResidual 2 ↥P = ⊤ := (isPComponent_two_iff.1 hP).2.1
    refine le_of_le_sup_pPrimeCore hP' hgen fun a ha => ?_
    have h1 : QuotientGroup.mk' (pPrimeCore 2 C) a ∈
        P'.map (QuotientGroup.mk' (pPrimeCore 2 C)) := hPP' ▸ ⟨a, ha, rfl⟩
    obtain ⟨a', ha', haa'⟩ := h1
    have h2 : a'⁻¹ * a ∈ pPrimeCore 2 C := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change (QuotientGroup.mk' (pPrimeCore 2 C) a')⁻¹ * QuotientGroup.mk' (pPrimeCore 2 C) a = 1
      rw [haa', inv_mul_cancel]
    have : a = a' * (a'⁻¹ * a) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ha' h2
  exact le_antisymm (hle hA hA' h) (hle hA' hA h.symm)

theorem mem_normalizer_of_conj_le {G : Type} [Group G] [Finite G] {H : Subgroup G} {c : G}
    (h : ∀ x ∈ H, c * x * c⁻¹ ∈ H) : c ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj c).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have hcard : Nat.card (H.map (MulAut.conj c).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  exact mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge hle hcard.ge)

variable {C : Type} [Group C] [Finite C]

theorem exists_diag_lift {B : Subgroup C} (hB : IsPComponent 2 B)
    (hZB : IsPGroup 2 ↥(center (↥B ⧸ pPrimeCore 2 ↥B)))
    {tr tw : C} (htr : tr * tr = 1) (hcomm : tw * tr = tr * tw)
    (hne : B.map (MulAut.conj tr).toMonoidHom ≠ B) (htw : ∀ b ∈ B, tw * b * tw⁻¹ ∈ B) :
    ∃ Δ : Subgroup C, Δ ≤ centralizer ({tr} : Set C) ∧
      IsPComponent 2 (Δ.subgroupOf (centralizer ({tr} : Set C))) ∧
      (∀ x ∈ Δ, tw * x * tw⁻¹ ∈ Δ) ∧
      ∀ OO W₂ : Subgroup C, Odd (Nat.card OO) → Δ ≤ normalizer (OO : Set C) →
        IsPGroup 2 ↥W₂ → W₂ ≤ normalizer (OO : Set C) → (∀ x ∈ Δ, ⁅x, tw⁆ ∈ OO ⊔ W₂) →
        ∀ b ∈ B, ⁅b, tw⁆ ∈ pPrimeCore 2 C := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : C →* C ⧸ pPrimeCore 2 C := QuotientGroup.mk' (pPrimeCore 2 C) with hπ
  set B' : Subgroup C := B.map (MulAut.conj tr).toMonoidHom with hB'
  have hB'pc : IsPComponent 2 B' :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 (MulAut.conj tr) hB
  have hK₁c : IsComponent (B.map π) := by
    obtain ⟨K, hK, -, hKeq, -⟩ := hB
    exact hKeq ▸ hK
  set g : C ⧸ pPrimeCore 2 C := π tr with hg
  have hg2 : g * g = 1 := by rw [hg, ← map_mul, htr, map_one]
  have hKK' : (B.map π).map (MulAut.conj g).toMonoidHom = B'.map π := by
    rw [Subgroup.map_map, hB', Subgroup.map_map]
    congr 1
  have hne' : (B.map π).map (MulAut.conj g).toMonoidHom ≠ B.map π := by
    rw [hKK']
    intro h
    exact hne (eq_of_map_pPrimeCore_eq hB'pc hB h)
  obtain ⟨D, δ, hDq, hDC, hDs, hDl, hδsur, hδv⟩ := diag_isComponent hK₁c hg2 hne'
  have hDmem : ∀ v ∈ B.map π, v * (g * v * g⁻¹) ∈ D := fun v hv => by
    have h1 := (δ ⟨v, hv⟩).2
    rw [hδv ⟨v, hv⟩] at h1
    exact h1
  have hZK : IsPGroup 2 ↥(center ↥(B.map π)) := by
    obtain ⟨e⟩ := exists_mulEquiv_quot_image hB
    exact hZB.of_equiv (centerCongr e)
  have hZD : IsPGroup 2 ↥(center ↥D) := isPGroup_center_of_surjective hK₁c.1 hDq hZK δ hδsur
  obtain ⟨Δ, hΔC, hΔpc, hΔmap, hΔn⟩ := exists_isPComponent_lift htr hDq hDC hDs
  have hjK : ∀ k ∈ B.map π, π tw * k * (π tw)⁻¹ ∈ B.map π := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨tw * b * tw⁻¹, htw b hb, by simp⟩
  have hjg : Commute (π tw) g := by
    change π tw * π tr = π tr * π tw
    rw [← map_mul, ← map_mul, hcomm]
  have hjgD : ∀ v : C ⧸ pPrimeCore 2 C, π tw * (v * (g * v * g⁻¹)) * (π tw)⁻¹ =
      (π tw * v * (π tw)⁻¹) * (g * (π tw * v * (π tw)⁻¹) * g⁻¹) := by
    intro v
    have e1 : π tw * g = g * π tw := hjg.eq
    calc π tw * (v * (g * v * g⁻¹)) * (π tw)⁻¹ =
        π tw * v * (π tw)⁻¹ * ((π tw * g) * v * (π tw * g)⁻¹) := by group
      _ = π tw * v * (π tw)⁻¹ * ((g * π tw) * v * (g * π tw)⁻¹) := by rw [e1]
      _ = (π tw * v * (π tw)⁻¹) * (g * (π tw * v * (π tw)⁻¹) * g⁻¹) := by group
  have hDn : ∀ d ∈ D, π tw * d * (π tw)⁻¹ ∈ D := by
    intro d hd
    obtain ⟨v, hv⟩ := hδsur ⟨d, hd⟩
    have hd' : d = (v : C ⧸ pPrimeCore 2 C) * (g * v * g⁻¹) := by
      have := hδv v
      rw [hv] at this
      exact this
    rw [hd', hjgD v]
    exact hDmem _ (hjK v v.2)
  have hπtwD : π tw ∈ normalizer (D : Set (C ⧸ pPrimeCore 2 C)) := mem_normalizer_of_conj_le hDn
  have htwC : tw ∈ centralizer ({tr} : Set C) := Subgroup.mem_centralizer_singleton_iff.2 hcomm
  have htwΔ : ∀ x ∈ Δ, tw * x * tw⁻¹ ∈ Δ := fun x hx =>
    (mem_normalizer_iff.1 (hΔn tw htwC hπtwD) x).1 hx
  refine ⟨Δ, hΔC, hΔpc, htwΔ, ?_⟩
  intro OO W₂ hOO hΔOO hW₂ hW₂OO hV b hb
  let ψ : ↥Δ →* ↥D := (π.comp Δ.subtype).codRestrict D (fun x => by
    rw [← hΔmap]
    exact Subgroup.mem_map_of_mem π x.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨d, hd⟩
    obtain ⟨x, hx, hxd⟩ := Subgroup.mem_map.1 (hΔmap ▸ hd)
    exact ⟨⟨x, hx⟩, Subtype.ext hxd⟩
  have hQ : ∀ M : Subgroup ↥D, M.Normal → Odd (Nat.card M) → M = ⊥ := fun M hM hodd => by
    have := hM
    exact normal_odd_eq_bot_of_quasisimple hDq hZD hodd
  obtain ⟨R, hRn, hRp, hRmem⟩ :=
    commutator_image_normal_two (X := C) ψ hψ htwΔ hOO hΔOO hW₂ hW₂OO hQ hV
  have hRc : R ≤ center ↥D := by
    have := hRn
    exact normal_pgroup_le_center_of_quasisimple hDq hRp
  have hcen : ∀ d ∈ D, ∀ y ∈ D, Commute y ⁅d, π tw⁆ := by
    intro d hd y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hΔmap ▸ hd)
    have hx' : ⁅x, tw⁆ ∈ Δ := by
      have e : ⁅x, tw⁆ = x * (tw * x⁻¹ * tw⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Δ.mul_mem hx (htwΔ _ (Δ.inv_mem hx))
    have h1 := hRc (hRmem ⟨x, hx⟩ hx')
    have h2 := Subgroup.mem_center_iff.1 h1 ⟨y, hy⟩
    have h3 : (π ⁅x, tw⁆ : C ⧸ pPrimeCore 2 C) = ⁅π x, π tw⁆ := map_commutatorElement π x tw
    have h4 := congrArg Subtype.val h2
    exact (by simpa [ψ, h3] using h4 : y * ⁅π x, π tw⁆ = ⁅π x, π tw⁆ * y)
  have hcomD := commute_of_central_comm (commutator_eq_self_of_quasisimple hDq) hDn
    (fun k hk y hy => by
      have e : k⁻¹ * (π tw * k * (π tw)⁻¹) = ⁅k⁻¹, π tw⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hcen _ (D.inv_mem hk) y hy)
  have hcenK := centralizes_of_comm_diag hK₁c hne' hjK hjg (fun v hv => hcomD _ (hDmem v hv))
  have hπb : π ⁅b, tw⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcenK _ ⟨b, hb, rfl⟩).symm.eq
  exact (QuotientGroup.eq_one_iff _).1 hπb

end DiagStep

end CFSG.OddStandard.Solomon75
