module

public import CFSG.GH74.GLS.LU.Local.SL2AutComm
public import CFSG.GH74.GLS.LU.Local.Torus3
public import CFSG.GH74.GLS.LU.Local.Torus5

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
  CFSG.ComponentClassification
open CFSG.Semidihedral.MatrixCoverData (slConjugation)
open scoped Pointwise MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

variable {G : Type} [Group G]

theorem actAut_of_mem {F : Type} [Field F] {K : Subgroup G} (e : SL(2, F) ≃* ↥K) {k : G} (hk : k ∈ K) :
    actAut e k (Subgroup.le_normalizer hk) = MulAut.conj (e.symm ⟨k, hk⟩) := by
  refine MulEquiv.ext fun M => ?_
  apply e.injective
  apply Subtype.ext
  rw [coe_actAut]
  simp [MulAut.conj_apply]

theorem slConjugation_fix_comm {F : Type} [Field F] (G' : GL (Fin 2) F) (k : SL(2, F))
    (h : slConjugation F G' k = k) :
    (G' : Matrix (Fin 2) (Fin 2) F) * (k : Matrix (Fin 2) (Fin 2) F) =
      (k : Matrix (Fin 2) (Fin 2) F) * (G' : Matrix (Fin 2) (Fin 2) F) := by
  have h' := congrArg (fun N : SL(2, F) => (N : Matrix (Fin 2) (Fin 2) F)) h
  simp only [slConjugation_coe] at h'
  have hinv : ((G'⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (G' : Matrix (Fin 2) (Fin 2) F) = 1 := Units.inv_mul G'
  calc (G' : Matrix (Fin 2) (Fin 2) F) * (k : Matrix (Fin 2) (Fin 2) F)
      = ((G' : Matrix (Fin 2) (Fin 2) F) * (k : Matrix (Fin 2) (Fin 2) F) *
          ((G'⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) * (G' : Matrix (Fin 2) (Fin 2) F) := by
        rw [Matrix.mul_assoc ((G' : Matrix (Fin 2) (Fin 2) F) * (k : Matrix (Fin 2) (Fin 2) F)), hinv,
          Matrix.mul_one]
    _ = (k : Matrix (Fin 2) (Fin 2) F) * (G' : Matrix (Fin 2) (Fin 2) F) := by rw [h']

variable [Finite G] {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t u : G} {p f : ℕ} {ε : ℤ}

theorem odd_of_mem_pPrimeCore_CY {x : G} {y : CY G x} (hy : y ∈ pPrimeCore 2 (CY G x)) :
    Odd (orderOf (y : G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : orderOf y ∣ Nat.card (pPrimeCore 2 (CY G x)) := Subgroup.orderOf_dvd_natCard _ hy
  have hodd : Odd (Nat.card (pPrimeCore 2 (CY G x))) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rw [Subgroup.orderOf_coe]
  exact Odd.of_dvd_nat hodd hdvd

theorem acts_commute_K₂ (X : LUCtx G p f z S K₁ K₂ t u ε) {r : ℕ} (hr : GoodR p f r) {k : G}
    (hk : k ∈ K₂) (hord : orderOf k = r) {d : G} (hdn : d ∈ normalizer (K₂ : Set G))
    (hdodd : Odd (orderOf d)) (hdk : d * k = k * d) (huk : u * k = k * u) :
    ∀ y ∈ K₂, (d * u * d⁻¹ * u⁻¹) * y = y * (d * u * d⁻¹ * u⁻¹) := by
  have hc := X.comps
  have hs := X.syl
  have hq := X.odd_q
  obtain ⟨hrp, hr2, hrne, hrf, hgood⟩ := hr
  have hun : u ∈ normalizer (K₂ : Set G) := u_norm₂ hc hs
  obtain ⟨F, hF, hFin, hFq, -⟩ := hc.sl₂
  obtain ⟨e⟩ := exists_mulEquiv_SL2 hc.sl₂ F hFq
  have hodd : Odd (Nat.card F) := by rw [hFq]; exact hq
  have h3 : 3 < p ^ f := lt_of_lt_of_le (by norm_num) X.hq
  have h3' : 3 < Nat.card F := by rw [hFq]; exact h3
  have hu2 : u * u = 1 := hs.u_sq
  have hkt_ord : orderOf (e.symm ⟨k, hk⟩) = r := by simp [hord]
  have hkt_nc : e.symm ⟨k, hk⟩ ∉ Subgroup.center SL(2, F) := by
    intro hcen
    have h1 : (⟨k, hk⟩ : ↥K₂) ∈ center ↥K₂ := by
      have := (mem_center_equiv_iff e (a := e.symm ⟨k, hk⟩)).mpr hcen
      simpa using this
    have h2 : ∀ g ∈ K₂, k * g = g * k := by
      intro g hg
      have := Subgroup.mem_center_iff.mp h1 ⟨g, hg⟩
      exact (congrArg Subtype.val this).symm
    have h3 : k ∈ zpowers z := mem_zpowers_of_centralizes₂ hc hk h2
    have h4 : orderOf k ∣ orderOf z := orderOf_dvd_of_mem_zpowers h3
    rw [hord, hs.z_inv] at h4
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp h4)
  have hβd : actAut e d hdn ^ orderOf d = 1 := by
    rw [← actAut_pow e hdn (orderOf d)]
    exact (actAut_eq_one_iff e _).mpr (fun y _ => by rw [pow_orderOf_eq_one, one_mul, mul_one])
  have hcommd : actAut e d hdn * MulAut.conj (e.symm ⟨k, hk⟩) =
      MulAut.conj (e.symm ⟨k, hk⟩) * actAut e d hdn := by
    rw [← actAut_of_mem e hk, ← actAut_mul e hdn (Subgroup.le_normalizer hk),
      ← actAut_mul e (Subgroup.le_normalizer hk) hdn]
    exact actAut_congr e _ _ hdk
  obtain ⟨Gd, hGd, hGdk⟩ := sl2_aut_matrix_form_of_commute X.hp hFq X.hp2 h3 hrp hr2 hrne hrf hgood
    (e.symm ⟨k, hk⟩) hkt_ord (actAut e d hdn) (m := orderOf d) hdodd hβd hcommd
  have hunc := u_not_cent hc hs hq (Or.inr rfl)
  have hαsq : actAut e u hun * actAut e u hun = 1 := by
    have h := (actHom e).map_mul ⟨u, hun⟩ ⟨u, hun⟩
    have h1 : (⟨u, hun⟩ * ⟨u, hun⟩ : ↥(normalizer (K₂ : Set G))) = 1 := Subtype.ext hu2
    rw [h1, map_one] at h
    exact h.symm
  have hαne : actAut e u hun ≠ 1 := by
    intro h
    obtain ⟨y, hy, hyc⟩ := hunc
    exact hyc ((actAut_eq_one_iff e hun).mp h y hy)
  have hu2' : ∃ n : ℕ, orderOf u = 2 ^ n := ⟨1, by rw [hs.u_ord]; norm_num⟩
  have hab := cenAb_C hc hs (Or.inr rfl) hs.u_mem_Cz hu2' hun hunc
  have hfix : ∀ a b : SL(2, F), actAut e u hun a = a → actAut e u hun b = b → a * b = b * a := by
    intro a b ha hb
    have h1 := (actAut_fixed_iff e hun a).mp ha
    have h2 := (actAut_fixed_iff e hun b).mp hb
    have := hab _ (e a).2 _ (e b).2 h1 h2
    apply e.injective
    apply Subtype.ext
    simpa using this
  obtain ⟨Gu, hGu, -⟩ := sl2_aut_matrix_form_of_involution hodd h3' _ hαsq hαne hfix
  have hcommu : actAut e u hun * MulAut.conj (e.symm ⟨k, hk⟩) =
      MulAut.conj (e.symm ⟨k, hk⟩) * actAut e u hun := by
    rw [← actAut_of_mem e hk, ← actAut_mul e hun (Subgroup.le_normalizer hk),
      ← actAut_mul e (Subgroup.le_normalizer hk) hun]
    exact actAut_congr e _ _ huk
  have hfixu : actAut e u hun (e.symm ⟨k, hk⟩) = e.symm ⟨k, hk⟩ :=
    slAutComm_apply_eq hrp hr2 _ hkt_ord _ hcommu
  have hGuk := slConjugation_fix_comm Gu (e.symm ⟨k, hk⟩) (by rw [← hGu]; exact hfixu)
  have hGdGu : (Gd : Matrix (Fin 2) (Fin 2) F) * (Gu : Matrix (Fin 2) (Fin 2) F) =
      (Gu : Matrix (Fin 2) (Fin 2) F) * (Gd : Matrix (Fin 2) (Fin 2) F) :=
    CFSG.GH74.GLS.IVK.Lifted.commute_of_commute_nonscalar _
      (CFSG.GH74.GLS.IVK.Lifted.nonscalar_of_not_mem_center _ hkt_nc) hGdk hGuk
  have hGcomm : Gd * Gu = Gu * Gd := Units.ext hGdGu
  have hβcomm : actAut e d hdn * actAut e u hun = actAut e u hun * actAut e d hdn := by
    rw [hGd, hGu, ← map_mul, ← map_mul, hGcomm]
  intro y hy
  obtain ⟨εN, hεN⟩ : ∃ εN : ↥(normalizer (K₂ : Set G)),
      εN = ⟨d, hdn⟩ * ⟨u, hun⟩ * ⟨d, hdn⟩⁻¹ * ⟨u, hun⟩⁻¹ := ⟨_, rfl⟩
  have hεNc : (εN : G) = d * u * d⁻¹ * u⁻¹ := by rw [hεN]; rfl
  have hε1 : actHom e εN = 1 := by
    rw [hεN]
    simp only [map_mul, map_inv]
    have hdd : actHom e (⟨d, hdn⟩ : ↥(normalizer (K₂ : Set G))) = actAut e d hdn := actHom_apply e _
    have huu : actHom e (⟨u, hun⟩ : ↥(normalizer (K₂ : Set G))) = actAut e u hun := actHom_apply e _
    rw [hdd, huu, hβcomm]; group
  have h := (actAut_eq_one_iff e εN.2).mp ((actHom_apply e εN).symm.trans hε1) y hy
  rw [hεNc] at h
  exact h

theorem hD1_CY (X : LUCtx G p f z S K₁ K₂ t u ε) {r : ℕ} (hr : GoodR p f r) {x : G}
    (hx : XData z K₁ K₂ x r) (hxu : u * x = x * u) :
    ∀ d ∈ pPrimeCore 2 (CY G x), (d : G) * z = z * (d : G) → u * (d : G) = (d : G) * u := by
  intro d hd hdz
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic ↥(A0 z) := X.eps.A0_cyc
  have hc := X.comps
  have hs := X.syl
  have hK := kcomp_CY X hx
  have hz2 : z * z = 1 := hs.z_sq
  have hu2 : u * u = 1 := hs.u_sq
  have hzu : z * u = u * z := hs.zu_comm
  have hdodd : Odd (orderOf (d : G)) := odd_of_mem_pPrimeCore_CY hd
  have hdC : (d : G) ∈ Cz z := mem_centralizer_singleton_iff.mpr hdz
  have hdx : (d : G) * x = x * (d : G) := mem_centralizer_singleton_iff.mp d.2
  obtain ⟨e1, e2⟩ := hc.odd_fix hdC hdodd
  have hdn₂ : (d : G) ∈ normalizer (K₂ : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr e2
  have hdK₁ : ∀ k ∈ K₁, (d : G) * k = k * (d : G) := by
    intro k hk
    have hkC : k ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.mpr (hx.c₁ k hk).symm
    have hkY : (⟨k, hkC⟩ : CY G x) ∈ K₁.subgroupOf (centralizer ({x} : Set G)) :=
      Subgroup.mem_subgroupOf.mpr hk
    have hds : d ∈ centralizer ({toCY hx.cz} : Set (CY G x)) := by
      rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact hdz
    have := comm_of_mem_pPrimeCore_of_mem_centralizer hK.norm hK.inf_bot hd hds hkY
    exact congrArg Subtype.val this
  obtain ⟨a, ha, k, hk, hxak, hkord⟩ := hx.dec
  have hdk : (d : G) * k = k * (d : G) := by
    have ha' : (d : G) * a * (d : G)⁻¹ ∈ A0 z :=
      (mem_normalizer_iff.mp (mem_normalizer_pPrimeCoreOf hdC) a).mp ha
    have hk' : (d : G) * k * (d : G)⁻¹ ∈ K₂ := conj_mem_of_mem_normalizer hdn₂ hk
    have hprod : ((d : G) * a * (d : G)⁻¹) * ((d : G) * k * (d : G)⁻¹) = a * k := by
      have h1 : ((d : G) * a * (d : G)⁻¹) * ((d : G) * k * (d : G)⁻¹) =
          (d : G) * (a * k) * (d : G)⁻¹ := by group
      rw [h1, ← hxak, hdx]; group
    obtain ⟨m, hm⟩ : ∃ m : G, m = a⁻¹ * ((d : G) * a * (d : G)⁻¹) := ⟨_, rfl⟩
    have hmA : m ∈ A0 z := by rw [hm]; exact (A0 z).mul_mem ((A0 z).inv_mem ha) ha'
    have hmk : m = k * ((d : G) * k * (d : G)⁻¹)⁻¹ := by
      have : a⁻¹ * ((d : G) * a * (d : G)⁻¹) =
          a⁻¹ * (a * k) * ((d : G) * k * (d : G)⁻¹)⁻¹ := by
        rw [← hprod]; group
      rw [hm, this]; group
    have hmK : m ∈ K₂ := by rw [hmk]; exact K₂.mul_mem hk (K₂.inv_mem hk')
    have hmc : ∀ y ∈ K₂, m * y = y * m := fun y hy =>
      mem_centralizer_iff.mp (hc.le_centralizer_A0 (Subgroup.mem_sup_right hy)) m hmA
    have hmz : m ∈ zpowers z := mem_zpowers_of_centralizes₂ hc hmK hmc
    have hmodd : Odd (orderOf m) := odd_orderOf_pPrimeCoreOf hmA
    have hm1 : m = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers hz2 hmz with h | h
      · exact h
      · exfalso
        rw [h, hs.z_inv] at hmodd
        exact absurd hmodd (by decide)
    have h1 : k = (d : G) * k * (d : G)⁻¹ := by
      rw [hm1] at hmk
      exact (mul_inv_eq_one.mp hmk.symm)
    calc (d : G) * k = ((d : G) * k * (d : G)⁻¹) * (d : G) := by group
      _ = k * (d : G) := by rw [← h1]
  have huk : u * k = k * u := by
    have hua : u * a = a * u := by
      have h := X.h61.u_cent a ha
      calc u * a = (u * a * u⁻¹) * u := by group
        _ = a * u := by rw [h]
    have hcu : Commute u (a⁻¹ * x) := (show Commute u a from hua).inv_right.mul_right
      (show Commute u x from hxu)
    have : a⁻¹ * x = k := by rw [hxak]; group
    rw [this] at hcu
    exact hcu.eq
  have hcomm₂ := acts_commute_K₂ X hr hk hkord hdn₂ hdodd hdk huk
  obtain ⟨ε₂, hε₂⟩ : ∃ ε₂ : G, ε₂ = (d : G) * u * (d : G)⁻¹ * u⁻¹ := ⟨_, rfl⟩
  have hcomm₂' : ∀ y ∈ K₂, ε₂ * y = y * ε₂ := by rw [hε₂]; exact hcomm₂
  have hεz : ε₂ * z = z * ε₂ := by
    rw [hε₂]
    have c1 : Commute z (d : G) := (show Commute (d : G) z from hdz).symm
    have c2 : Commute z u := hzu
    exact ((((c1.mul_right c2).mul_right c1.inv_right).mul_right c2.inv_right).eq).symm
  have hεK₁ : ∀ k ∈ K₁, ε₂ * k = k * ε₂ := by
    intro k hk
    have hk₁ : u⁻¹ * k * u ∈ K₁ := conj_inv_mem_of_mem_normalizer hs.u_norm hk
    have h1 := hdK₁ k hk
    have h2 := hdK₁ _ hk₁
    have h2' : (d : G)⁻¹ * (u⁻¹ * k * u) = (u⁻¹ * k * u) * (d : G)⁻¹ := by
      calc (d : G)⁻¹ * (u⁻¹ * k * u) = (d : G)⁻¹ * ((u⁻¹ * k * u) * (d : G)) * (d : G)⁻¹ := by group
        _ = (d : G)⁻¹ * ((d : G) * (u⁻¹ * k * u)) * (d : G)⁻¹ := by rw [h2]
        _ = (u⁻¹ * k * u) * (d : G)⁻¹ := by group
    calc ε₂ * k = (d : G) * u * ((d : G)⁻¹ * (u⁻¹ * k * u)) * u⁻¹ := by rw [hε₂]; group
      _ = (d : G) * u * ((u⁻¹ * k * u) * (d : G)⁻¹) * u⁻¹ := by rw [h2']
      _ = (d : G) * k * (u * (d : G)⁻¹ * u⁻¹) := by group
      _ = k * (d : G) * (u * (d : G)⁻¹ * u⁻¹) := by rw [h1]
      _ = k * ε₂ := by rw [hε₂]; group
  have hεCCK : ε₂ ∈ CCK z K₁ K₂ := by
    refine mem_CCK.mpr ⟨mem_centralizer_singleton_iff.mpr hεz, fun k hk => ?_⟩
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := mem_sup_of_commute hc.comm hk
    have e₁ := hεK₁ a₁ ha₁
    have e₂ := hcomm₂' b₁ hb₁
    calc ε₂ * (a₁ * b₁) = (ε₂ * a₁) * b₁ := by group
      _ = (a₁ * ε₂) * b₁ := by rw [e₁]
      _ = a₁ * (ε₂ * b₁) := by group
      _ = a₁ * (b₁ * ε₂) := by rw [e₂]
      _ = (a₁ * b₁) * ε₂ := by group
  have hεodd : Odd (orderOf ε₂) := by
    have hu : u ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr hxu
    have hN : (pPrimeCore 2 (CY G x)).Normal := pPrimeCore_normal
    have h1 : d * (⟨u, hu⟩ * d⁻¹ * ⟨u, hu⟩⁻¹) ∈ pPrimeCore 2 (CY G x) :=
      (pPrimeCore 2 (CY G x)).mul_mem hd (hN.conj_mem _ ((pPrimeCore 2 (CY G x)).inv_mem hd) _)
    have := odd_of_mem_pPrimeCore_CY h1
    have e : (((d * (⟨u, hu⟩ * d⁻¹ * ⟨u, hu⟩⁻¹) : CY G x)) : G) = ε₂ := by
      have h0 : (((d * (⟨u, hu⟩ * d⁻¹ * ⟨u, hu⟩⁻¹) : CY G x)) : G) =
          (d : G) * (u * (d : G)⁻¹ * u⁻¹) := rfl
      rw [h0, hε₂]; group
    rwa [e] at this
  have hεA : ε₂ ∈ A0 z := odd_mem_A0_of_centralizes hs hc hεCCK hεodd
  have hcent : u * ε₂ * u⁻¹ = ε₂ := X.h61.u_cent ε₂ hεA
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hu2i : u⁻¹ * u⁻¹ = 1 := by rw [hui]; exact hu2
  have hinv : u * ε₂ * u⁻¹ = ε₂⁻¹ := by
    have e1 : u * ε₂ * u⁻¹ = u * (d : G) * u * (d : G)⁻¹ * (u⁻¹ * u⁻¹) := by rw [hε₂]; group
    have e2 : ε₂⁻¹ = u * (d : G) * u⁻¹ * (d : G)⁻¹ := by rw [hε₂]; group
    rw [e1, e2, hu2i, hui, mul_one]
  have hsq : ε₂ * ε₂ = 1 := by
    have : ε₂ = ε₂⁻¹ := by rw [← hinv, hcent]
    calc ε₂ * ε₂ = ε₂ * ε₂⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel ε₂
  have hε1 : ε₂ = 1 := by
    have h2 : orderOf ε₂ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      rw [h] at hεodd
      exact absurd hεodd (by decide)
  rw [hε₂] at hε1
  calc u * (d : G) = (d : G) * u * (d : G)⁻¹ * u⁻¹ * u * (d : G) := by
        rw [hε1]; group
    _ = (d : G) * u := by group

end CFSG.GH74.GLS.LU.Local
