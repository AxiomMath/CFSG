module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapContraComp
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma34
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapB

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.LocalCores
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

namespace ZPerm

section Center

variable {C : Type} [Group C] [Finite C]

theorem mem_pPrimeCore_of_mem_pPrimeCore {C' : Subgroup C} {y : ↥C'}
    (hy : (y : C) ∈ pPrimeCore 2 C) : y ∈ pPrimeCore 2 ↥C' := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup ↥C' := (pPrimeCore 2 C).subgroupOf C' with hM
  have hMnormal : M.Normal := Subgroup.Normal.subgroupOf pPrimeCore_normal C'
  have hMcard : Nat.Coprime 2 (Nat.card M) := by
    have hdvd : Nat.card M ∣ Nat.card (pPrimeCore 2 C) := Subgroup.card_dvd_of_injective
      (⟨⟨fun x => ⟨(x.1 : C), x.2⟩, rfl⟩, fun _ _ => rfl⟩ : M →* ↥(pPrimeCore 2 C)) (by
        intro a b hab
        exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥(pPrimeCore 2 C) => (t : C)) hab)))
    exact Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card
  have hMle : M ≤ pPrimeCore 2 ↥C' := le_sSup ⟨hMnormal, hMcard⟩
  exact hMle hy

theorem isPGroup_center_image_of_lift {C' P : Subgroup C} (hP : IsPCompIn 2 C' P)
    (hQ : IsQuasisimple ↥(P.map (QuotientGroup.mk' (pPrimeCore 2 C))))
    (hZ : IsPGroup 2 ↥(center ↥(P.map (QuotientGroup.mk' (pPrimeCore 2 C))))) :
    IsPGroup 2 ↥(center ↥((P.subgroupOf C').map (QuotientGroup.mk' (pPrimeCore 2 ↥C')))) := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC' : P ≤ C' := hP.1
  set π : C →* C ⧸ pPrimeCore 2 C := QuotientGroup.mk' (pPrimeCore 2 C) with hπ
  set π' : ↥C' →* ↥C' ⧸ pPrimeCore 2 ↥C' := QuotientGroup.mk' (pPrimeCore 2 ↥C') with hπ'
  set Q : Subgroup (C ⧸ pPrimeCore 2 C) := P.map π with hQdef
  set Q' : Subgroup (↥C' ⧸ pPrimeCore 2 ↥C') := (P.subgroupOf C').map π' with hQ'def
  have hQ'c : IsComponent Q' := by
    obtain ⟨K, hK, -, hKeq, -⟩ := hP.2
    show IsComponent ((P.subgroupOf C').map π')
    rw [hKeq]
    exact hK
  let ψ₁ : ↥P →* ↥Q := (π.comp P.subtype).codRestrict Q (fun x => Subgroup.mem_map_of_mem π x.2)
  let ψ₂ : ↥P →* ↥Q' := (π'.comp (Subgroup.inclusion hPC')).codRestrict Q' (fun x =>
    Subgroup.mem_map_of_mem π' (show Subgroup.inclusion hPC' x ∈ P.subgroupOf C' from x.2))
  have hψ₁ : Function.Surjective ψ₁ := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
    exact ⟨⟨x, hx⟩, rfl⟩
  have hψ₂ : Function.Surjective ψ₂ := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
    exact ⟨⟨(x : C), hx⟩, rfl⟩
  have hker : ψ₁.ker ≤ ψ₂.ker := by
    intro x hx
    have h1 : π (x : C) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      exact this
    have h2 : (x : C) ∈ pPrimeCore 2 C := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : Subgroup.inclusion hPC' x ∈ pPrimeCore 2 ↥C' :=
      mem_pPrimeCore_of_mem_pPrimeCore (C' := C') (y := Subgroup.inclusion hPC' x) h2
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).2 h3
  let φ : ↥Q →* ↥Q' := (MonoidHom.liftOfSurjective ψ₁ hψ₁) ⟨ψ₂, hker⟩
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := hψ₂ y
    exact ⟨ψ₁ x, by simpa [φ] using hx⟩
  exact isPGroup_center_of_surjective hQ hQ'c.1 hZ φ hφ

end Center

section DiagPair

variable {C : Type} [Group C] [Finite C]

theorem commute_mul_mul_of_commute {W : Type*} [Group W] {a a' b b' : W}
    (h1 : Commute a b) (h2 : Commute a b') (h3 : Commute a' b) (h4 : Commute a' b') :
    Commute (a * a') (b * b') :=
  (h1.mul_right h2).mul_left (h3.mul_right h4)

theorem exists_diag_lift_two {B : Subgroup C} (hB : IsPComponent 2 B)
    (hZB : IsPGroup 2 ↥(center (↥B ⧸ pPrimeCore 2 ↥B)))
    {tr tw : C} (htr : tr * tr = 1) (htw2 : tw * tw = 1) (hcomm : tw * tr = tr * tw)
    (hne : B.map (MulAut.conj tr).toMonoidHom ≠ B)
    (hw : B.map (MulAut.conj tw).toMonoidHom ≠ B)
    (hwr : B.map (MulAut.conj tw).toMonoidHom ≠ B.map (MulAut.conj tr).toMonoidHom) :
    ∃ Δ : Subgroup C, Δ ≤ centralizer ({tr} : Set C) ∧
      IsPComponent 2 (Δ.subgroupOf (centralizer ({tr} : Set C))) ∧
      ∀ OO W₂ : Subgroup C, Odd (Nat.card OO) →
        centralizer ({tr} : Set C) ≤ normalizer (OO : Set C) → IsPGroup 2 ↥W₂ →
        W₂ ≤ normalizer (OO : Set C) →
        (∀ x ∈ Δ ⊔ Δ.map (MulAut.conj tw).toMonoidHom, ⁅x, tw⁆ ∈ OO ⊔ W₂) → False := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : C →* C ⧸ pPrimeCore 2 C := QuotientGroup.mk' (pPrimeCore 2 C) with hπ
  set B' : Subgroup C := B.map (MulAut.conj tr).toMonoidHom with hB'
  set B'' : Subgroup C := B.map (MulAut.conj tw).toMonoidHom with hB''
  have hB'pc : IsPComponent 2 B' :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 (MulAut.conj tr) hB
  have hB''pc : IsPComponent 2 B'' :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 (MulAut.conj tw) hB
  have hK₁c : IsComponent (B.map π) := by
    obtain ⟨K, hK, -, hKeq, -⟩ := hB
    exact hKeq ▸ hK
  set g : C ⧸ pPrimeCore 2 C := π tr with hg
  set j : C ⧸ pPrimeCore 2 C := π tw with hj
  have hg2 : g * g = 1 := by rw [hg, ← map_mul, htr, map_one]
  have hjg : j * g = g * j := by rw [hj, hg, ← map_mul, ← map_mul, hcomm]
  have hKK' : (B.map π).map (MulAut.conj g).toMonoidHom = B'.map π := by
    rw [Subgroup.map_map, hB', Subgroup.map_map]
    congr 1
  have hKKj : (B.map π).map (MulAut.conj j).toMonoidHom = B''.map π := by
    rw [Subgroup.map_map, hB'', Subgroup.map_map]
    congr 1
  have hne' : (B.map π).map (MulAut.conj g).toMonoidHom ≠ B.map π := by
    rw [hKK']
    intro h
    exact hne (eq_of_map_pPrimeCore_eq hB'pc hB h)
  have hnej : (B.map π).map (MulAut.conj j).toMonoidHom ≠ B.map π := by
    rw [hKKj]
    intro h
    exact hw (eq_of_map_pPrimeCore_eq hB''pc hB h)
  have hnejg : (B.map π).map (MulAut.conj j).toMonoidHom ≠
      (B.map π).map (MulAut.conj g).toMonoidHom := by
    rw [hKKj, hKK']
    intro h
    exact hwr (eq_of_map_pPrimeCore_eq hB''pc hB'pc h)
  obtain ⟨D, δ, hDq, hDC, hDs, -, hδsur, hδv⟩ := diag_isComponent hK₁c hg2 hne'
  have hZK : IsPGroup 2 ↥(center ↥(B.map π)) := by
    obtain ⟨e⟩ := exists_mulEquiv_quot_image hB
    exact hZB.of_equiv (centerCongr e)
  have hZD : IsPGroup 2 ↥(center ↥D) := isPGroup_center_of_surjective hK₁c.1 hDq hZK δ hδsur
  obtain ⟨Δ, hΔC, hΔpc, hΔmap, -⟩ := exists_isPComponent_lift htr hDq hDC hDs
  set C' : Subgroup C := centralizer ({tr} : Set C) with hC'
  have htwC' : tw ∈ C' := Subgroup.mem_centralizer_singleton_iff.2 hcomm
  have hΔ'le : Δ.map (MulAut.conj tw).toMonoidHom ≤ C' := by
    rintro _ ⟨x, hx, rfl⟩
    show tw * x * tw⁻¹ ∈ C'
    exact C'.mul_mem (C'.mul_mem htwC' (hΔC hx)) (C'.inv_mem htwC')
  have hΔ'pc : IsPComponent 2 ((Δ.map (MulAut.conj tw).toMonoidHom).subgroupOf C') := by
    have h1 := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
      (MulAut.conj (⟨tw, htwC'⟩ : ↥C')) hΔpc
    rwa [map_conj_subgroupOf htwC' Δ] at h1
  have hΔmap' : (Δ.map (MulAut.conj tw).toMonoidHom).map π =
      D.map (MulAut.conj j).toMonoidHom := by
    rw [← hΔmap, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hDe := Subgroup.equivMapOfInjective D (MulAut.conj j).toMonoidHom (MulAut.conj j).injective
  have hDq' : IsQuasisimple ↥(D.map (MulAut.conj j).toMonoidHom) :=
    isQuasisimple_of_mulEquiv hDe hDq
  have hZD' : IsPGroup 2 ↥(center ↥(D.map (MulAut.conj j).toMonoidHom)) :=
    hZD.of_equiv (centerCongr hDe)
  have hZΔ : IsPGroup 2
      ↥(center ↥((Δ.subgroupOf C').map (QuotientGroup.mk' (pPrimeCore 2 ↥C')))) :=
    isPGroup_center_image_of_lift ⟨hΔC, hΔpc⟩ (by rw [hΔmap]; exact hDq)
      (by rw [hΔmap]; exact hZD)
  have hZΔ' : IsPGroup 2 ↥(center ↥(((Δ.map (MulAut.conj tw).toMonoidHom).subgroupOf C').map
      (QuotientGroup.mk' (pPrimeCore 2 ↥C')))) :=
    isPGroup_center_image_of_lift ⟨hΔ'le, hΔ'pc⟩ (by rw [hΔmap']; exact hDq')
      (by rw [hΔmap']; exact hZD')
  have hΔne : Δ.map (MulAut.conj tw).toMonoidHom ≠ Δ := by
    intro heq
    have hDj : D.map (MulAut.conj j).toMonoidHom = D := by
      rw [← hΔmap', heq, hΔmap]
    have hmm : ∀ H : Subgroup (C ⧸ pPrimeCore 2 C),
        (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = H := fun H =>
      map_conj_map_conj (fun x _ => by rw [pow_two, hg2, one_mul, mul_one])
    have hKjc : IsComponent ((B.map π).map (MulAut.conj j).toMonoidHom) :=
      isComponent_map_mulEquiv (MulAut.conj j) hK₁c
    have hKgc : IsComponent ((B.map π).map (MulAut.conj g).toMonoidHom) :=
      isComponent_map_mulEquiv (MulAut.conj g) hK₁c
    have hKjgc : IsComponent (((B.map π).map (MulAut.conj j).toMonoidHom).map
        (MulAut.conj g).toMonoidHom) := isComponent_map_mulEquiv (MulAut.conj g) hKjc
    have hKKjg : B.map π ≠ ((B.map π).map (MulAut.conj j).toMonoidHom).map
        (MulAut.conj g).toMonoidHom := by
      intro h
      have h1 := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h
      rw [hmm] at h1
      exact hnejg h1.symm
    have hKgKjg : (B.map π).map (MulAut.conj g).toMonoidHom ≠ ((B.map π).map
        (MulAut.conj j).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      intro h
      have h1 := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h
      rw [hmm, hmm] at h1
      exact hnej h1.symm
    apply center_ne_top_of_isQuasisimple_aux hDq
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨v, hv⟩ := hδsur y
    have hy : (y : C ⧸ pPrimeCore 2 C) = (v : C ⧸ pPrimeCore 2 C) * (g * v * g⁻¹) := by
      have := hδv v
      rw [hv] at this
      exact this
    have hxD : (x : C ⧸ pPrimeCore 2 C) ∈ D.map (MulAut.conj j).toMonoidHom := by
      rw [hDj]
      exact x.2
    obtain ⟨x₁, hx₁D, hx₁⟩ := Subgroup.mem_map.1 hxD
    obtain ⟨w, hw'⟩ := hδsur ⟨x₁, hx₁D⟩
    have hx₁eq : x₁ = (w : C ⧸ pPrimeCore 2 C) * (g * w * g⁻¹) := by
      have := hδv w
      rw [hw'] at this
      exact this
    have hxeq : (x : C ⧸ pPrimeCore 2 C) =
        (j * w * j⁻¹) * (g * (j * w * j⁻¹) * g⁻¹) := by
      rw [← hx₁]
      show j * x₁ * j⁻¹ = _
      rw [hx₁eq]
      have e : g * (j * w * j⁻¹) * g⁻¹ = j * (g * w * g⁻¹) * j⁻¹ := by
        calc g * (j * w * j⁻¹) * g⁻¹ = (g * j) * w * (g * j)⁻¹ := by group
          _ = (j * g) * w * (j * g)⁻¹ := by rw [hjg]
          _ = j * (g * w * g⁻¹) * j⁻¹ := by group
      rw [e]
      group
    have hc1 : Commute (v : C ⧸ pPrimeCore 2 C) (j * w * j⁻¹) :=
      commute_of_ne hK₁c hKjc (fun e => hnej e.symm) v.2 (conj_mem_map_conj w.2)
    have hc2 : Commute (v : C ⧸ pPrimeCore 2 C) (g * (j * w * j⁻¹) * g⁻¹) :=
      commute_of_ne hK₁c hKjgc hKKjg v.2 (conj_mem_map_conj (conj_mem_map_conj w.2))
    have hc3 : Commute (g * v * g⁻¹) (j * w * j⁻¹) :=
      commute_of_ne hKgc hKjc (fun e => hnejg e.symm) (conj_mem_map_conj v.2)
        (conj_mem_map_conj w.2)
    have hc4 : Commute (g * v * g⁻¹) (g * (j * w * j⁻¹) * g⁻¹) :=
      commute_of_ne hKgc hKjgc hKgKjg (conj_mem_map_conj v.2)
        (conj_mem_map_conj (conj_mem_map_conj w.2))
    have hc := commute_mul_mul_of_commute hc1 hc2 hc3 hc4
    apply Subtype.ext
    show (y : C ⧸ pPrimeCore 2 C) * x = x * y
    rw [hy, hxeq]
    exact hc.eq
  refine ⟨Δ, hΔC, hΔpc, ?_⟩
  intro OO W₂ hOO hCn hW₂ hW₂OO hV
  have hΛle : Δ ⊔ Δ.map (MulAut.conj tw).toMonoidHom ≤ C' := sup_le hΔC hΔ'le
  exact swap_contra_comp htw2 ⟨hΔC, hΔpc⟩ ⟨hΔ'le, hΔ'pc⟩ hΔne hZΔ hZΔ' hOO (hΛle.trans hCn)
    hW₂ hW₂OO hV

end DiagPair

section OTwo

variable {X : Type} [Group X] [Finite X]

theorem le_oTwoPrimeOf_of_isPCompIn {H K M : Subgroup X} (hK : IsPCompIn 2 H K) (hKM : K ≤ M) :
    K ≤ oTwoPrimeOf M := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hres : primeResidual 2 ↥K = ⊤ := ((pComponent_subgroupOf_iff 2 K H hK.1).1 hK.2).2.1
  exact (oTwoPrimeOf_eq_self_of_primeResidual hres).symm.le.trans (oTwoPrimeOf_mono hKM)

omit [Finite X] in
theorem mem_normalizer_oTwoPrimeOf {W : Subgroup X} {g : X} (hg : g ∈ normalizer (W : Set X)) :
    g ∈ normalizer (oTwoPrimeOf W : Set X) :=
  oTwoPrimeOf_normalizes (A := Subgroup.zpowers g) (H := W) (Subgroup.zpowers_le.2 hg)
    (Subgroup.mem_zpowers g)

theorem commutator_decomp_of_mirror_two {s r : X} {Zs : Subgroup X} (hsZs : s ∈ Zs)
    (hrs : r * s = s * r)
    (hL34 : oTwoPrimeOf (LPlusIn (centralizer ({r} : Set X))) ≤
      pPrimeCoreOf 2 (LPlusIn (centralizer ({r} : Set X))) ⊔
        (normalizer (Zs : Set X) ⊓ LPlusIn (centralizer ({r} : Set X))))
    {x : X} (hx : x ∈ oTwoPrimeOf (LPlusIn (centralizer ({r} : Set X)))) :
    ∃ o ∈ pPrimeCoreOf 2 (LPlusIn (centralizer ({r} : Set X))),
      ∃ w ∈ Zs ⊓ centralizer ({r} : Set X), ⁅x, s⁆ = o * w := by
  set L : Subgroup X := LPlusIn (centralizer ({r} : Set X)) with hL
  set 𝒪 : Subgroup X := pPrimeCoreOf 2 L with h𝒪
  have hLC : L ≤ centralizer ({r} : Set X) := LPlusIn_le _
  have hCn : centralizer ({r} : Set X) ≤ normalizer (𝒪 : Set X) :=
    (le_normalizer_LPlusIn _).trans (normalizer_le_normalizer_pPrimeCoreOf L)
  have hsC : s ∈ centralizer ({r} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hrs.symm
  have hx' : x ∈ 𝒪 ⊔ (normalizer (Zs : Set X) ⊓ L) := hL34 hx
  obtain ⟨o, ho, y, hy, hxy⟩ := (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing 𝒪
    (normalizer (Zs : Set X) ⊓ L) (fun y hy => hCn (hLC hy.2)) x).1 hx'
  have hw'Zs : y * s * y⁻¹ ∈ Zs := (Subgroup.mem_normalizer_iff.1 hy.1 s).1 hsZs
  have hw'C : y * s * y⁻¹ ∈ centralizer ({r} : Set X) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLC hy.2) hsC) (Subgroup.inv_mem _ (hLC hy.2))
  refine ⟨o * ((y * s * y⁻¹) * o⁻¹ * (y * s * y⁻¹)⁻¹), 𝒪.mul_mem ho ?_, (y * s * y⁻¹) * s⁻¹,
    ⟨Zs.mul_mem hw'Zs (Zs.inv_mem hsZs), Subgroup.mul_mem _ hw'C (Subgroup.inv_mem _ hsC)⟩, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 (hCn hw'C) o⁻¹).1 (𝒪.inv_mem ho)
  · rw [← hxy]; simp only [commutatorElement_def]; group

end OTwo

end ZPerm

section Main

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

theorem zPerm_of_moved (h : Sec5Data X n z Z S) (hs : IsSec5Inv X Z s)
    (hZs : Z ≤ centralizer ({s} : Set X)) {u : X} (huZ : u ∈ Z) (hu1 : u ≠ 1) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B)
    (hBu : B.map (MulAut.conj u).toMonoidHom ≠ B) {r : X} (hrZ : r ∈ Z) :
    B.map (MulAut.conj r).toMonoidHom = B ∨
      B.map (MulAut.conj r).toMonoidHom = B.map (MulAut.conj u).toMonoidHom := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hrB, hru⟩ := hcon
  set Cs : Subgroup X := centralizer ({s} : Set X) with hCs
  have hs2' : s ^ 2 = 1 := by rw [sq]; exact hs.sq
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  have hu2o : orderOf u = 2 := h.orderOf_eq_two_of_mem_Z huZ hu1
  have hr2 : r * r = 1 := h.Z_sq_eq_one hrZ
  have huN : u ∈ normalizer (Z : Set X) := Subgroup.le_normalizer huZ
  have hur : r * u = u * r := h.Z_comm hrZ huZ
  have huC : u ∈ Cs := hZs huZ
  have hrC : r ∈ Cs := hZs hrZ
  have hsu : s * u = u * s := (Subgroup.mem_centralizer_singleton_iff.1 huC).symm
  have hBCs : B ≤ Cs := hB.isPCompIn.1
  have hmapC : ∀ c ∈ Cs, B.map (MulAut.conj c).toMonoidHom ≤ Cs := by
    intro c hc
    rintro _ ⟨b, hb, rfl⟩
    exact Cs.mul_mem (Cs.mul_mem hc (hBCs hb)) (Cs.inv_mem hc)
  have hBc : IsPComponent 2 (B.subgroupOf Cs) := hB.isPCompIn.2
  have hZB := hB.isPGroup_center_quot
  set trc : ↥Cs := ⟨u, huC⟩ with htrc
  set twc : ↥Cs := ⟨r, hrC⟩ with htwc
  have htr : trc * trc = 1 := Subtype.ext hu2
  have htw : twc * twc = 1 := Subtype.ext hr2
  have hcomm : twc * trc = trc * twc := Subtype.ext hur
  have hne : (B.subgroupOf Cs).map (MulAut.conj trc).toMonoidHom ≠ B.subgroupOf Cs := by
    rw [map_conj_subgroupOf huC B]
    intro heq
    apply hBu
    have h1 := heq
    rw [Subgroup.subgroupOf_inj, inf_of_le_left (hmapC u huC), inf_of_le_left hBCs] at h1
    exact h1
  have hw : (B.subgroupOf Cs).map (MulAut.conj twc).toMonoidHom ≠ B.subgroupOf Cs := by
    rw [map_conj_subgroupOf hrC B]
    intro heq
    apply hrB
    have h1 := heq
    rw [Subgroup.subgroupOf_inj, inf_of_le_left (hmapC r hrC), inf_of_le_left hBCs] at h1
    exact h1
  have hwr : (B.subgroupOf Cs).map (MulAut.conj twc).toMonoidHom ≠
      (B.subgroupOf Cs).map (MulAut.conj trc).toMonoidHom := by
    rw [map_conj_subgroupOf hrC B, map_conj_subgroupOf huC B]
    intro heq
    apply hru
    have h1 := heq
    rw [Subgroup.subgroupOf_inj, inf_of_le_left (hmapC r hrC),
      inf_of_le_left (hmapC u huC)] at h1
    exact h1
  obtain ⟨Δ, hΔC, hΔpc, hkey⟩ := ZPerm.exists_diag_lift_two hBc hZB htr htw hcomm hne hw hwr
  set ΔX : Subgroup X := Δ.map Cs.subtype with hΔX
  have hΔXs : ΔX ≤ Cs := Subgroup.map_subtype_le Δ
  have hΔXu : ΔX ≤ centralizer ({u} : Set X) := by
    rintro _ ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hΔC hx)
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  have hcenmap : (centralizer ({trc} : Set ↥Cs)).map Cs.subtype =
      Cs ⊓ centralizer ({u} : Set X) := by
    rw [centralizer_singleton_subgroup huC, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hΔXpc : IsPCompIn 2 (Cs ⊓ centralizer ({u} : Set X)) ΔX := by
    refine ⟨le_inf hΔXs hΔXu, ?_⟩
    have h1 := (isPComponent_subgroupOf_map_iff 2 Cs.subtype Cs.subtype_injective hΔC).2 hΔpc
    rwa [hcenmap] at h1
  have hΔL : ΔX ≤ oTwoPrimeOf (LPlusIn (centralizer ({u} : Set X))) :=
    ZPerm.le_oTwoPrimeOf_of_isPCompIn hΔXpc (le_LPlusIn_of_isPCompIn_inf hs2' hsu hΔXpc)
  have hJ0 : K0 X n (K0 X n (normalizer (Z : Set X)) ⊓ centralizer ({u} : Set X)) ≠ ⊥ := by
    obtain ⟨A₀, hA₀, -⟩ := h.exists_comp
    have hscj : u ∈ centralizerSection A₀ (pPrimeCoreOf 2 A₀) := by
      refine normalizes_isPCompIn_of_comm_mem hA₀.isPCompIn (Subgroup.le_normalizer huN)
        (fun l hl => ?_)
      have hlK : l ∈ K0 X n (normalizer (Z : Set X)) := (le_sSup hA₀ : A₀ ≤ _) hl
      have : ⁅l, u⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.2 (h.Z_le_center_K0 huZ hlK).symm
      rw [this]
      exact one_mem _
    exact K0_ne_bot_of_centralizerSection (by rw [sq]; exact hu2) hA₀ hscj
  have hL34 := lemma34_oTwoPrimeOf h.hypA h.maxdeg h.pair huN hu2o hJ0
  set OO : Subgroup X := pPrimeCoreOf 2 (LPlusIn (centralizer ({u} : Set X))) with hOO
  set W₂ : Subgroup X := Z ⊓ centralizer ({u} : Set X) with hW₂
  have hCn : centralizer ({u} : Set X) ≤ normalizer (OO : Set X) :=
    (le_normalizer_LPlusIn _).trans (normalizer_le_normalizer_pPrimeCoreOf _)
  have hOOodd : Odd (Nat.card OO) := odd_card_oddCoreOf _
  have hW₂p : IsPGroup 2 ↥W₂ := h.isPGroup_Z.to_le inf_le_left
  set OOc : Subgroup ↥Cs := OO.comap Cs.subtype with hOOc
  set W₂c : Subgroup ↥Cs := W₂.comap Cs.subtype with hW₂c
  have hOOcodd : Odd (Nat.card OOc) := by
    refine Odd.of_dvd_nat hOOodd (Subgroup.card_dvd_of_injective
      (⟨⟨fun x => ⟨(x.1 : X), x.2⟩, rfl⟩, fun _ _ => rfl⟩ : OOc →* ↥OO) ?_)
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥OO => (t : X)) hab))
  have hW₂cp : IsPGroup 2 ↥W₂c := by
    refine hW₂p.of_injective (⟨⟨fun x => ⟨(x.1 : X), x.2⟩, rfl⟩, fun _ _ => rfl⟩ : W₂c →* ↥W₂) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥W₂ => (t : X)) hab))
  have hconjOO : ∀ y : ↥Cs, (y : X) ∈ centralizer ({u} : Set X) →
      y ∈ normalizer (OOc : Set ↥Cs) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro t
    exact mem_normalizer_iff.1 (hCn hy) (t : X)
  have hCnc : centralizer ({trc} : Set ↥Cs) ≤ normalizer (OOc : Set ↥Cs) := by
    intro y hy
    refine hconjOO y ?_
    have := Subgroup.mem_centralizer_singleton_iff.1 hy
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  have hW₂OO : W₂c ≤ normalizer (OOc : Set ↥Cs) := fun x hx => hconjOO x hx.2
  have hru' : r ∈ centralizer ({u} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hur
  have hrn : r ∈ normalizer (oTwoPrimeOf (LPlusIn (centralizer ({u} : Set X))) : Set X) :=
    ZPerm.mem_normalizer_oTwoPrimeOf (le_normalizer_LPlusIn _ hru')
  have hΛL : Δ ⊔ Δ.map (MulAut.conj twc).toMonoidHom ≤
      (oTwoPrimeOf (LPlusIn (centralizer ({u} : Set X)))).comap Cs.subtype := by
    refine sup_le (fun x hx => hΔL ⟨x, hx, rfl⟩) ?_
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hrn (y : X)).1 (hΔL ⟨y, hy, rfl⟩)
  have hV : ∀ x ∈ Δ ⊔ Δ.map (MulAut.conj twc).toMonoidHom, ⁅x, twc⁆ ∈ OOc ⊔ W₂c := by
    intro x hx
    have hxX : (x : X) ∈ oTwoPrimeOf (LPlusIn (centralizer ({u} : Set X))) := hΛL hx
    obtain ⟨o, ho, w', hw', hxw⟩ :=
      ZPerm.commutator_decomp_of_mirror_two hrZ hur.symm hL34 hxX
    have hw'C : w' ∈ Cs := hZs hw'.1
    have hcx : (((⁅x, twc⁆ : ↥Cs)) : X) = ⁅(x : X), r⁆ := by
      simp [commutatorElement_def, htwc]
    have hoC : o ∈ Cs := by
      have : o = (((⁅x, twc⁆ : ↥Cs)) : X) * w'⁻¹ := by rw [hcx, hxw]; group
      rw [this]
      exact Cs.mul_mem (⁅x, twc⁆ : ↥Cs).2 (Cs.inv_mem hw'C)
    have hprod : ⁅x, twc⁆ = (⟨o, hoC⟩ : ↥Cs) * ⟨w', hw'C⟩ :=
      Subtype.ext (by rw [hcx, hxw]; rfl)
    rw [hprod]
    exact Subgroup.mul_mem_sup (show (⟨o, hoC⟩ : ↥Cs) ∈ OOc from ho)
      (show (⟨w', hw'C⟩ : ↥Cs) ∈ W₂c from hw')
  exact hkey OOc W₂c hOOcodd hCnc hW₂cp hW₂OO hV

end Main

end CFSG.OddStandard.Solomon75
