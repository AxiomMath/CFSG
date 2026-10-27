module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.GenCore
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporComp
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Phi
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieQuasi

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

theorem le_of_forall_mem_mul_coprime {D N O P : Subgroup G} (hND : N ≤ D)
    (hNn : (N.subgroupOf D).Normal) (hOD : O ≤ D) (hcopO : Nat.Coprime 3 (Nat.card ↥O))
    (hDNO : ∀ d ∈ D, ∃ n ∈ N, ∃ u ∈ O, d = n * u) (hPD : P ≤ D)
    (hPq : CFSG.Open.IsQuasisimple ↥P) (hP3 : 3 ∣ Nat.card (↥P ⧸ Subgroup.center ↥P)) :
    P ≤ N := by
  haveI := hNn
  let θ : ↥P →* ↥D ⧸ N.subgroupOf D :=
    (QuotientGroup.mk' (N.subgroupOf D)).comp (Subgroup.inclusion hPD)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (isQuasisimple_native' hPq)
    (inferInstance : θ.ker.Normal) with htop | hcen
  · intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ θ.ker := htop ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at this
    have h1 : (⟨x, hPD hx⟩ : ↥D) ∈ N.subgroupOf D := (QuotientGroup.eq_one_iff _).1 this
    exact h1
  · exfalso
    have hcard : 3 ∣ Nat.card θ.range := by
      rw [← Subgroup.index_ker]
      have h1 : (Subgroup.center ↥P).index ∣ θ.ker.index := Subgroup.index_dvd_of_le hcen
      exact (show 3 ∣ (Subgroup.center ↥P).index from hP3).trans h1
    have hle : θ.range ≤ ((O.subgroupOf D).map (QuotientGroup.mk' (N.subgroupOf D))) := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨n, hn, u, hu, hxu⟩ := hDNO x (hPD x.2)
      refine ⟨⟨u, hOD hu⟩, hu, ?_⟩
      show (QuotientGroup.mk (⟨u, hOD hu⟩ : ↥D) : ↥D ⧸ N.subgroupOf D) =
        QuotientGroup.mk (⟨(x : G), hPD x.2⟩ : ↥D)
      have : (⟨(x : G), hPD x.2⟩ : ↥D) = ⟨n, hND hn⟩ * ⟨u, hOD hu⟩ := Subtype.ext hxu
      rw [this, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (⟨n, hND hn⟩ : ↥D)).2 hn]
      simp
    have hdvd : Nat.card θ.range ∣ Nat.card ↥O := by
      refine (Subgroup.card_dvd_of_le hle).trans ?_
      refine (Subgroup.card_map_dvd _ _).trans ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOD).toEquiv]
    have := Nat.Coprime.coprime_dvd_right hdvd hcopO
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 this hcard

theorem three_dvd_card_quotient_center {J : Type*} [Group J] [Finite J] (hperf : commutator J = ⊤)
    (h3 : 3 ∣ Nat.card J) : 3 ∣ Nat.card (J ⧸ Subgroup.center J) := by
  by_contra hnd
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)
  have hZ3 : 3 ∣ Nat.card (Subgroup.center J) := by
    rw [hmul] at h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
    · exact absurd h hnd
    · exact h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center J)) 3 hZ3
  have hzo : orderOf (z : J) = 3 := by rw [Subgroup.orderOf_coe, hz]
  have hz1 := false_of_perfect_of_central_mem_abelian hperf (P := Subgroup.center J)
    (fun a ha b hb => Subgroup.mem_center_iff.1 hb a) z.2 z.2
    (by rw [hzo]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd |>.symm)
  rw [hz1, orderOf_one] at hzo
  omega

theorem normal_of_comm_components {C J : Subgroup G} (hJC : J ≤ C)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hJ3 : 3 ∣ Nat.card ↥J)
    (hB : ∀ M : Subgroup G, GLAPComponent 3 C M → ∀ g ∈ M, ∀ o ∈ GLAPPrimeCoreOf 3 C,
      o * g = g * o)
    (hD : ((J ⊔ GLAPPrimeCoreOf 3 C).subgroupOf C).Normal) : (J.subgroupOf C).Normal := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set O := GLAPPrimeCoreOf 3 C with hO
  have hOC : O ≤ C := glaPPrimeCoreOf_le C
  have hcopO : Nat.Coprime 3 (Nat.card ↥O) := coprime_card_glaPPrimeCoreOf C
  have hOn : ∀ c ∈ C, ∀ o ∈ O, c * o * c⁻¹ ∈ O := fun c hc o ho => conj_mem_glaPPrimeCoreOf hc ho
  set D := J ⊔ O with hDdef
  have hDC : D ≤ C := sup_le hJC hOC
  have hJD : J ≤ D := le_sup_left
  have hOD : O ≤ D := le_sup_right
  have hsnD : IsSubnormal D C := IsSubnormal.step hDC hD (IsSubnormal.refl C)
  have hJ3' : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    three_dvd_card_quotient_center hJq.1 hJ3
  have hJnorm : J ≤ Subgroup.normalizer (O : Set G) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hOn j (hJC hj) n hn, fun hn => ?_⟩
    have := hOn j⁻¹ (C.inv_mem (hJC hj)) _ hn
    simpa [mul_assoc] using this
  have hcoreD : GLAPPrimeCoreOf 3 D = O := by
    refine le_antisymm (glaPPrimeCoreOf_le_of_isSubnormal hp hsnD) ?_
    exact le_glaPPrimeCoreOf hOD (fun a ha n hn => conj_mem_glaPPrimeCoreOf (hDC ha) hn) hcopO
  have hOmem : ∀ u (hu : u ∈ O), (⟨u, hOD hu⟩ : ↥D) ∈ GLAPPrimeCore 3 ↥D := fun u hu => by
    have hu' : u ∈ GLAPPrimeCoreOf 3 D := hcoreD ▸ hu
    exact (mem_glaPPrimeCoreOf_iff.1 hu').2
  have hJOz : ∀ (x : G) (hx : x ∈ J), x ∈ O → (⟨x, hx⟩ : ↥J) ∈ Subgroup.center ↥J := by
    have hN1 : ((J ⊓ O).subgroupOf J).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2), hOn (g : G) (hJC g.2) _ hn.2⟩⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups (isQuasisimple_native' hJq) hN1 with
      htop | hcen
    · exfalso
      have hJO : J ≤ O := by
        intro x hx
        have : (⟨x, hx⟩ : ↥J) ∈ (J ⊓ O).subgroupOf J := htop ▸ Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.1 this).2
      have h1 : 3 ∣ Nat.card ↥O := hJ3.trans (Subgroup.card_dvd_of_le hJO)
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcopO h1
    · intro x hx hxO
      exact hcen (Subgroup.mem_subgroupOf.2 ⟨hx, hxO⟩)
  let f : ↥J →* ↥D ⧸ GLAPPrimeCore 3 ↥D :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥D)).comp (Subgroup.inclusion hJD)
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨j, hj, u, hu, hdu⟩ := ia_exists_mul_of_mem_sup hJnorm d.2
    refine ⟨⟨j, hj⟩, ?_⟩
    show (QuotientGroup.mk (⟨j, hJD hj⟩ : ↥D) : ↥D ⧸ GLAPPrimeCore 3 ↥D) = QuotientGroup.mk d
    have hd : d = ⟨j, hJD hj⟩ * ⟨u, hOD hu⟩ := Subtype.ext hdu
    rw [hd, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (⟨u, hOD hu⟩ : ↥D)).2 (hOmem u hu)]
    simp
  have hfker : f.ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (⟨(x : G), hJD x.2⟩ : ↥D) ∈ GLAPPrimeCore 3 ↥D := (QuotientGroup.eq_one_iff _).1 hx
    have h2 : (x : G) ∈ GLAPPrimeCoreOf 3 D := mem_glaPPrimeCoreOf_iff.2 ⟨hJD x.2, h1⟩
    rw [hcoreD] at h2
    exact hJOz x x.2 h2
  have hQD : CFSG.Open.IsQuasisimple (↥D ⧸ GLAPPrimeCore 3 ↥D) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
      (CFSG.LocalCores.isQuasisimple_of_surjective (isQuasisimple_native' hJq) f hfsurj hfker)
  obtain ⟨I, hI, htop, -⟩ := exists_glaPComponent_of_isQuasisimple hQD
  have hIC : GLAPComponent 3 C I := ia_comp_up hp hI hDC (isSubnormal_trans' hI.2.1 hsnD)
  have hIO : ∀ g ∈ I, ∀ o ∈ O, o * g = g * o := hB I hIC
  have hDIO : ∀ d ∈ D, ∃ n ∈ I, ∃ u ∈ O, d = n * u := by
    intro d hd
    have hmem : (QuotientGroup.mk (⟨d, hd⟩ : ↥D) : ↥D ⧸ GLAPPrimeCore 3 ↥D) ∈ barX 3 D I := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨i, hi, hie⟩ := Subgroup.mem_map.1 hmem
    have h1 : i⁻¹ * ⟨d, hd⟩ ∈ GLAPPrimeCore 3 ↥D := QuotientGroup.eq.1 hie
    have h2 : ((i⁻¹ * ⟨d, hd⟩ : ↥D) : G) ∈ GLAPPrimeCoreOf 3 D :=
      mem_glaPPrimeCoreOf_iff.2 ⟨(i⁻¹ * ⟨d, hd⟩ : ↥D).2, h1⟩
    rw [hcoreD] at h2
    exact ⟨(i : G), hi, (i : G)⁻¹ * d, h2, by group⟩
  have hIn : ∀ d ∈ D, ∀ n ∈ I, d * n * d⁻¹ ∈ I := by
    intro d hd n hn
    obtain ⟨i, hi, u, hu, rfl⟩ := hDIO d hd
    have hcu : u * n = n * u := hIO n hn u hu
    have h1 : i * u * n * (i * u)⁻¹ = i * n * i⁻¹ := by
      calc i * u * n * (i * u)⁻¹ = i * (u * n) * u⁻¹ * i⁻¹ := by group
        _ = i * (n * u) * u⁻¹ * i⁻¹ := by rw [hcu]
        _ = i * n * i⁻¹ := by group
    rw [h1]
    exact I.mul_mem (I.mul_mem hi hn) (I.inv_mem hi)
  have hINn : (I.subgroupOf D).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hIn (g : G) g.2 (n : G) hn⟩
  have hJI : J ≤ I := le_of_forall_mem_mul_coprime hI.1 hINn hOD hcopO hDIO hJD hJq hJ3'
  have hJO : ∀ j ∈ J, ∀ o ∈ O, o * j = j * o := fun j hj o ho => hIO j (hJI hj) o ho
  have hJDJO : ∀ d ∈ D, ∃ n ∈ J, ∃ u ∈ O, d = n * u := fun d hd =>
    ia_exists_mul_of_mem_sup hJnorm hd
  have hJn : ∀ d ∈ D, ∀ x ∈ J, d * x * d⁻¹ ∈ J := by
    intro d hd x hx
    obtain ⟨j, hj, u, hu, rfl⟩ := hJDJO d hd
    have hcu : u * x = x * u := hJO x hx u hu
    have h1 : j * u * x * (j * u)⁻¹ = j * x * j⁻¹ := by
      calc j * u * x * (j * u)⁻¹ = j * (u * x) * u⁻¹ * j⁻¹ := by group
        _ = j * (x * u) * u⁻¹ * j⁻¹ := by rw [hcu]
        _ = j * x * j⁻¹ := by group
    rw [h1]
    exact J.mul_mem (J.mul_mem hj hx) (J.inv_mem hj)
  have hJNn : (J.subgroupOf D).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hJn (g : G) g.2 (n : G) hn⟩
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  set f₀ : G →* G := (MulAut.conj (g : G)).toMonoidHom with hf₀def
  have hf₀ : Function.Injective f₀ := (MulAut.conj (g : G)).injective
  set J' : Subgroup G := J.map f₀ with hJ'
  have hJ'D : J' ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact hD.conj_mem ⟨x, hJC hx⟩ (show (⟨x, hJC hx⟩ : ↥C) ∈ D.subgroupOf C from hJD hx) g
  have hJ'q : CFSG.Open.IsQuasisimple ↥J' :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (J.equivMapOfInjective f₀ hf₀) hJq
  have hJ'3 : 3 ∣ Nat.card ↥J' := by
    rw [hJ', Subgroup.card_map_of_injective hf₀]; exact hJ3
  have hJ'3' : 3 ∣ Nat.card (↥J' ⧸ Subgroup.center ↥J') :=
    three_dvd_card_quotient_center hJ'q.1 hJ'3
  have hJ'J : J' ≤ J :=
    le_of_forall_mem_mul_coprime hJD hJNn hOD hcopO hJDJO hJ'D hJ'q hJ'3'
  exact hJ'J ⟨n, hn, rfl⟩

theorem comm_components_of_b3S {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    (hK3 : GLAPPrimeCore 3 ↥K = ⊥) {b : Y} (hbK : b ∈ Subgroup.normalizer (K : Set Y))
    (hb3 : b ^ 3 = 1)
    (hB : ∀ β : MulAut (↥K ⧸ Subgroup.center ↥K), β ^ 3 = 1 →
      ⁅GLAPLayer 3 (fixSubgroup β), GLAPPrimeCoreOf 3 (fixSubgroup β)⁆ = ⊥) :
    ∀ M : Subgroup Y, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) M →
      ∀ g ∈ M, ∀ o ∈ GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)),
        o * g = g * o := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  let α₀ : MulAut ↥K := K.normalizerMonoidHom ⟨b, hbK⟩
  have hα₀ : ∀ k : ↥K, ((α₀ k : ↥K) : Y) = b * k * b⁻¹ := fun k => rfl
  have hα₀3 : α₀ ^ 3 = 1 := by
    have h0 : α₀ ^ 3 =
        K.normalizerMonoidHom ((⟨b, hbK⟩ : ↥(Subgroup.normalizer (K : Set Y))) ^ 3) := by
      rw [map_pow]
    rw [h0]
    have h1 : (⟨b, hbK⟩ : ↥(Subgroup.normalizer (K : Set Y))) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hb3)
    rw [h1, map_one]
  let Z := Subgroup.center ↥K
  let π : ↥K →* ↥K ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := (QuotientGroup.ker_mk' _).le
  have hmap : Z.map α₀.toMonoidHom = Z := Subgroup.characteristic_iff_map_eq.1 inferInstance α₀
  let β : MulAut (↥K ⧸ Z) := QuotientGroup.congr Z Z α₀ hmap
  have hαβ : ∀ k, π (α₀ k) = β (π k) := fun k => rfl
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨k, rfl⟩ := hπ q
    rw [← b3Lie_intertwine_pow π α₀ β hαβ, hα₀3]
    rfl
  have hBβ := hB β hβ3
  set X : Subgroup ↥K := fixSubgroup α₀ with hX
  have hXmap : X.map K.subtype = K ⊓ Subgroup.centralizer ({b} : Set Y) := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      have h1 : b * (k : Y) * b⁻¹ = k := by
        have := congrArg Subtype.val (show α₀ k = k from hk)
        rwa [hα₀] at this
      refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      show (k : Y) * b = b * (k : Y)
      calc (k : Y) * b = (b * (k : Y) * b⁻¹) * b := by rw [h1]
        _ = b * (k : Y) := by group
    · rintro ⟨hyK, hyC⟩
      refine ⟨⟨y, hyK⟩, ?_, rfl⟩
      show α₀ ⟨y, hyK⟩ = ⟨y, hyK⟩
      apply Subtype.ext
      rw [hα₀]
      have hyC' : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
      show b * y * b⁻¹ = y
      calc b * y * b⁻¹ = (y * b) * b⁻¹ := by rw [hyC']
        _ = y := by group
  intro M hM g hg o ho
  have hM0 : GLAPComponent 3 (X.map K.subtype) M := by rw [hXmap]; exact hM
  have hc : ∀ y ∈ X ⊓ K.subtype.ker, ∀ z ∈ X, z * y = y * z := by
    intro y hy z _
    have : y = 1 := Subtype.ext (MonoidHom.mem_ker.1 hy.2)
    rw [this, mul_one, one_mul]
  obtain ⟨M₁, hM₁, hM₁map⟩ := exists_glaPComponent_map_central hp K.subtype hc hM0
  have hMβ : GLAPComponent 3 (fixSubgroup β) (M₁.map π) :=
    glaPComponent_map_fixSubgroup π hker α₀ β hαβ hπ hp hM₁
  have hOmap := map_glaPPrimeCoreOf_fixSubgroup_le π hker α₀ β hαβ hπ hp
  have hO : GLAPPrimeCoreOf 3 (X.map K.subtype) = (GLAPPrimeCoreOf 3 X).map K.subtype :=
    (CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective 3 K.subtype
      K.subtype_injective X).symm
  rw [hXmap] at hO
  rw [hO] at ho
  obtain ⟨o₁, ho₁, rfl⟩ := ho
  rw [← hM₁map] at hg
  obtain ⟨g₁, hg₁, rfl⟩ := hg
  have hcomm := comm_of_b3Phi hBβ hMβ (π g₁) ⟨g₁, hg₁, rfl⟩ (π o₁) (hOmap ⟨o₁, ho₁, rfl⟩)
  have hg₁X : g₁ ∈ X := hM₁.1 hg₁
  set c : ↥K := o₁ * g₁ * o₁⁻¹ * g₁⁻¹ with hcdef
  have hcZ : c ∈ Subgroup.center ↥K := by
    apply hker
    rw [MonoidHom.mem_ker, hcdef]
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  have hcO : c ∈ GLAPPrimeCoreOf 3 X := by
    have h1 : g₁ * o₁⁻¹ * g₁⁻¹ ∈ GLAPPrimeCoreOf 3 X :=
      conj_mem_glaPPrimeCoreOf hg₁X ((GLAPPrimeCoreOf 3 X).inv_mem ho₁)
    have h2 := (GLAPPrimeCoreOf 3 X).mul_mem ho₁ h1
    have e : o₁ * (g₁ * o₁⁻¹ * g₁⁻¹) = c := by rw [hcdef]; group
    rwa [e] at h2
  have hnorm : (Subgroup.zpowers c).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : n ∈ Subgroup.center ↥K := (Subgroup.zpowers_le.2 hcZ) hn
    have := Subgroup.mem_center_iff.1 hn' g
    rw [this, mul_inv_cancel_right]
    exact hn
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers c)) :=
    (coprime_card_glaPPrimeCoreOf X).coprime_dvd_right
      (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hcO))
  have hmem : c ∈ GLAPPrimeCore 3 ↥K :=
    le_sSup (show Subgroup.zpowers c ∈ {N : Subgroup ↥K | N.Normal ∧ Nat.Coprime 3 (Nat.card N)}
      from ⟨hnorm, hcop⟩) (Subgroup.mem_zpowers c)
  rw [hK3, Subgroup.mem_bot] at hmem
  have h1 : o₁ * g₁ = g₁ * o₁ := by
    have : o₁ * g₁ * o₁⁻¹ * g₁⁻¹ = 1 := hmem
    calc o₁ * g₁ = (o₁ * g₁ * o₁⁻¹ * g₁⁻¹) * (g₁ * o₁) := by group
      _ = g₁ * o₁ := by rw [this, one_mul]
  exact congrArg Subtype.val h1

theorem lieIndexChar_eq_characteristic (d : TauCeti.LieTypeIndex) :
    lieIndexChar d = d.characteristic := by
  cases d <;> simp [lieIndexChar]

theorem b3_chevTwo_of_semisimpleCent (hss : LieSemisimpleCent) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (hS : IsChevTwo S)
    (β : MulAut S) (hβ : β ^ 3 = 1) :
    ⁅GLAPLayer 3 (fixSubgroup β), GLAPPrimeCoreOf 3 (fixSubgroup β)⁆ = ⊥ := by
  haveI := hs
  by_cases hβ1 : β = 1
  · subst hβ1
    exact commutator_glaPLayer_eq_bot_of_perfect_le_layer (perfectInLayer_one hnc)
  obtain ⟨idx, hidx, ⟨e⟩⟩ := hS
  have hchar : (3 : ℕ) ≠ idx.1.characteristic := by
    rw [← lieIndexChar_eq_characteristic, lieIndexChar_eq_two_of_isCharTwoLieIndex hidx]
    norm_num
  exact commutator_glaPLayer_eq_bot_of_perfect_le_layer
    (hss S hs hnc idx ⟨e⟩ 3 Nat.prime_three (by norm_num) hchar β hβ hβ1)

theorem genNormality_of_semisimpleCent (hss : LieSemisimpleCent) : GenNormality := by
  intro Y _ _ K E J hKq hK3 hKc hEN hEel hE9 hJle hJn hJq h3 b hb hb1 hD
  have hbK : b ∈ Subgroup.normalizer (K : Set Y) := hEN hb
  have hb3 : b ^ 3 = 1 := hEel.2 b hb
  have hJC : J ≤ K ⊓ Subgroup.centralizer ({b} : Set Y) := fun x hx =>
    ⟨(hJle hx).1, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 (hJle hx).2 b hb).symm⟩
  have hB := comm_components_of_b3S hK3 hbK hb3 fun β hβ =>
    b3_chevTwo_of_semisimpleCent hss hKq.2
      (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥K hKq) hKc β hβ
  exact normal_of_comm_components hJC hJq h3 hB hD

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
