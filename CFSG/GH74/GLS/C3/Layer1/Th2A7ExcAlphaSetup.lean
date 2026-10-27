module

public import CFSG.GH74.GLS.C3.Layer1.Th2A7ExcNc
public import CFSG.GH74.GLS.C3.Layer1.Th2A7ExcAlphaStep
public import CFSG.GH74.GLS.C3.Layer1.BkA7Facts
public import CFSG.GH74.GLS.C3.Layer1.Th2A7ExcAux
public import CFSG.GH74.GLS.C3.Layer1.Th2P43fPerm
public import CFSG.GH74.GLS.C3.Layer1.Th2Struct

public section

namespace CFSG.GH74.GLS.Th2.AlphaStep

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1.Bk CFSG.GH74.GLS.C3.Layer1.Back
  CFSG.GH74.GLS.C3.Layer1.U1a Equiv Equiv.Perm CFSG.LieType.SteinbergBR.SmallAlt
  CFSG.GH74.GLS.Th2.P43f
open scoped commutatorElement

structure AlphaSetup {G : Type} [Group G] (x : G) (K T : Subgroup G) (a z : G)
    (psi : G → Perm (Fin 7)) : Prop where
  psiD : PsiData (centralizer ({x} : Set G)) K psi
  psi_ker : ∀ g ∈ centralizer ({x} : Set G), psi g = 1 ↔ g ∈ CxK x K
  psi_P : ∀ u ∈ T ⊓ K, ∃ i : Fin 8, psi u = a7P i
  psi_P_surj : ∀ i : Fin 8, ∃ u ∈ T ⊓ K, psi u = a7P i
  P_inv : ∀ u ∈ T ⊓ K, psi u * psi u = 1 → u * u = 1
  T_le_C : T ≤ centralizer ({x} : Set G)
  x_sq : x * x = 1
  x_ne : x ≠ 1
  x_mem_T : x ∈ T
  psi_x : psi x = 1
  z_mem : z ∈ T ⊓ K
  z_ne : z ≠ 1
  z_sq : z * z = 1
  z_central : ∀ t ∈ T, z * t = t * z
  psi_z : psi z = a7P 1
  hxz : a * z * a⁻¹ = x
  hxa : a * x * a⁻¹ = z
  haa : a * a ∈ T
  Pa_le : (T ⊓ K).map (MulAut.conj a).toMonoidHom ≤ T
  comm : ∀ p ∈ T ⊓ K, ∀ q ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom, p * q = q * p
  disj : (T ⊓ K) ⊓ (T ⊓ K).map (MulAut.conj a).toMonoidHom = ⊥
  T_eq : T = (T ⊓ K) ⊔ (T ⊓ K).map (MulAut.conj a).toMonoidHom
  Q_invol : ∀ u ∈ T ⊓ CxK x K, u * u = 1 → u = 1 ∨ u = x

theorem exists_alphaSetup {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x y : G}
    {K T S : Subgroup G} (hs : Th2Std x y K T S) (e7 : kBar K ≃* alternatingGroup (Fin 7))
    {T' S' : Subgroup G} {a : G} (hw : IsExcA7Witness x K T' S' a)
    (hα : T' ⊓ CxK x K ≤ (T' ⊓ K).map (MulAut.conj a).toMonoidHom) :
    ∃ (z : G) (psi : G → Perm (Fin 7)), AlphaSetup x K T' a z psi := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hT'C, hT'N, -, -, -, -, -, -, ha2, -, hdisj, hcomm, hTeq, ⟨eP⟩, ⟨eQ⟩⟩ := hw
  have hcen : CenterlessBar K := centerlessBar_of_A7 ⟨e7⟩
  have hT2 : IsPGroup 2 ↥T' := hT'C.isPGroup
  have hTC : T' ≤ centralizer ({x} : Set G) := hT'C.le
  have hP2 : 2 ≤ pRank 2 ↥(T ⊓ K) :=
    two_le_pRank_of_isD8 (isD8_of_inf_alt7 hs.T_pGroup hs.sylow_P e7)
  have hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K :=
    hs.K_normal (by rw [hG.pRank_eq_four]) hcen hP2
  have hP' : IsSylowOf 2 (T' ⊓ K) K := by
    have h1 := hT'N.inf_of_le_normalizer hs.K_le_NxK (fun n hn => hn.2)
    rwa [inf_assoc, inf_eq_right.2 hs.K_le_NxK] at h1
  obtain ⟨ψ, hker, hψK⟩ := lemma113d_alt hs.K_le_C hKN (n := 7) (by norm_num) (by norm_num) e7
  have hker' : ψ.ker =
      (CMK (centralizer ({x} : Set G)) K).subgroupOf (centralizer ({x} : Set G)) := hker
  obtain ⟨ι, hιinj, hιcard, hι⟩ := inf_embeds_alt7 hT2 hP' e7
  obtain ⟨c, hc1, hc2⟩ := exists_conj_model (X := ι.range) hιcard
  obtain ⟨cP, hcP⟩ : ∃ cP : Perm (Fin 7), cP = (c : Perm (Fin 7)) := ⟨_, rfl⟩
  let psi : G → Perm (Fin 7) := fun g =>
    if hg : g ∈ centralizer ({x} : Set G) then cP⁻¹ * (ψ ⟨g, hg⟩ : Perm (Fin 7)) * cP else 1
  have hpsiC : ∀ g (hg : g ∈ centralizer ({x} : Set G)),
      psi g = cP⁻¹ * (ψ ⟨g, hg⟩ : Perm (Fin 7)) * cP := fun g hg => by
    simp only [psi, hg, dite_true]
  have hpsimul : ∀ g ∈ centralizer ({x} : Set G), ∀ h ∈ centralizer ({x} : Set G),
      psi (g * h) = psi g * psi h := by
    intro g hg h hh
    rw [hpsiC _ ((centralizer ({x} : Set G)).mul_mem hg hh), hpsiC g hg, hpsiC h hh]
    have : ψ ⟨g * h, (centralizer ({x} : Set G)).mul_mem hg hh⟩ = ψ ⟨g, hg⟩ * ψ ⟨h, hh⟩ :=
      map_mul ψ ⟨g, hg⟩ ⟨h, hh⟩
    rw [this]
    group
  have hconjone : ∀ u : Perm (Fin 7), cP⁻¹ * u * cP = 1 ↔ u = 1 := by
    intro u
    constructor
    · intro h
      calc u = cP * (cP⁻¹ * u * cP) * cP⁻¹ := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  have hpsiker : ∀ g ∈ centralizer ({x} : Set G), psi g = 1 ↔ g ∈ CxK x K := by
    intro g hg
    rw [hpsiC g hg, hconjone, ← MonoidHom.mem_ker, hker', Subgroup.mem_subgroupOf]
    rfl
  have hpsiKker : ∀ k ∈ K, psi k = 1 ↔ k ∈ pPrimeCoreOf 2 K := by
    intro k hk
    have hkC : k ∈ centralizer ({x} : Set G) := hs.K_le_C hk
    rw [hpsiC k hkC, hconjone, hψK k hk]
    constructor
    · intro h
      have h2' : e7 (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K) = 1 := Subtype.ext h
      have h2 : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K) = 1 :=
        e7.injective (h2'.trans (map_one e7).symm)
      exact Setup91.mem_pPrimeCoreOf_iff.2 ⟨hk, (QuotientGroup.eq_one_iff _).1 h2⟩
    · intro h
      obtain ⟨hk', h2⟩ := Setup91.mem_pPrimeCoreOf_iff.1 h
      have h3 : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : kBar K) = 1 := (QuotientGroup.eq_one_iff _).2 h2
      rw [h3, map_one]
      rfl
  have hpsisurj : ∀ h : Perm (Fin 7), sign h = 1 → ∃ k ∈ K, psi k = h := by
    intro h hh
    have hh' : cP * h * cP⁻¹ ∈ alternatingGroup (Fin 7) := by
      rw [mem_alternatingGroup, map_mul, map_mul, hh, map_inv]
      have : sign cP = 1 := by rw [hcP]; exact mem_alternatingGroup.1 c.2
      rw [this]
      simp
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (e7.symm ⟨cP * h * cP⁻¹, hh'⟩)
    refine ⟨(q : G), q.2, ?_⟩
    have hqC : (q : G) ∈ centralizer ({x} : Set G) := hs.K_le_C q.2
    rw [hpsiC _ hqC]
    have h1 : ψ ⟨(q : G), hqC⟩ =
        ((e7 (QuotientGroup.mk q) : alternatingGroup (Fin 7)) : Perm (Fin 7)) :=
      hψK (q : G) q.2
    rw [h1, hq, MulEquiv.apply_symm_apply]
    simp only
    group
  have hιψ : ∀ p : ↥(T' ⊓ K), ((ι p : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ψ ⟨(p : G), hTC p.2.1⟩ := by
    intro p
    rw [hι p]
    exact (hψK p p.2.2).symm
  have hpsiP : ∀ u ∈ T' ⊓ K, ∃ i : Fin 8, psi u = a7P i := by
    intro u hu
    have hmem : ι ⟨u, hu⟩ ∈ ι.range := ⟨⟨u, hu⟩, rfl⟩
    obtain ⟨i, hi⟩ := hc2 _ hmem
    refine ⟨i, ?_⟩
    rw [hpsiC u (hTC hu.1), ← hιψ ⟨u, hu⟩]
    have hi' : a7P i = cP⁻¹ * ((ι ⟨u, hu⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) * cP := by
      rw [hcP]
      simpa using hi
    exact hi'.symm
  have hpsiPsurj : ∀ i : Fin 8, ∃ u ∈ T' ⊓ K, psi u = a7P i := by
    intro i
    have hy : (⟨a7P i, mem_alternatingGroup.2 (a7P_sign i)⟩ : alternatingGroup (Fin 7)) ∈
        CFSG.LieType.SteinbergBR.SmallAlt.finSubgroup a7P a7P_mul a7P_inv a7P_one := ⟨i, rfl⟩
    obtain ⟨p, hp⟩ := hc1 _ hy
    refine ⟨(p : G), p.2, ?_⟩
    rw [hpsiC _ (hTC p.2.1), ← hιψ p, hp]
    have hp' : (((c * ⟨a7P i, mem_alternatingGroup.2 (a7P_sign i)⟩ * c⁻¹ :
        alternatingGroup (Fin 7)) : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
        cP * a7P i * cP⁻¹ := by
      rw [hcP]
      simp
    rw [hp']
    group
  have hYodd : ∀ y ∈ pPrimeCoreOf 2 K, Odd (orderOf y) := fun y hy =>
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K) (Subgroup.orderOf_dvd_natCard _ hy)
  have hPsiD : PsiData (centralizer ({x} : Set G)) K psi :=
    { K_le := hs.K_le_C
      K_norm := hKN
      mul := hpsimul
      ker_odd := fun k hk h => hYodd k ((hpsiKker k hk).1 h)
      surj := hpsisurj }
  have hPinv : ∀ u ∈ T' ⊓ K, psi u * psi u = 1 → u * u = 1 := by
    intro u hu h
    have huC : u ∈ centralizer ({x} : Set G) := hTC hu.1
    have h1 : psi (u * u) = 1 := by rw [hpsimul u huC u huC]; exact h
    have hmemK : u * u ∈ K := K.mul_mem hu.2 hu.2
    have hodd : Odd (orderOf (u * u)) := hPsiD.ker_odd _ hmemK h1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT2) (⟨u * u, T'.mul_mem hu.1 hu.1⟩ : ↥T')
    rw [Subgroup.orderOf_mk] at hk
    have hk0 : k = 0 := by
      by_contra hk0
      have : Even (2 ^ k) := Nat.even_pow.2 ⟨even_two, hk0⟩
      rw [← hk] at this
      exact (Nat.not_even_iff_odd.2 hodd) this
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.1 hk
  have hxx : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hs.orderOf_x, sq] at h
    exact h
  have hx1 : x ≠ 1 := by
    intro h
    have := hs.orderOf_x
    rw [h, orderOf_one] at this
    omega
  have hxT' : x ∈ T' :=
    C3.Layer1.Back.mem_of_isSylowOf_of_central hT'C (mem_centralizer_singleton_iff.2 rfl)
      (fun _ hs' => mem_centralizer_singleton_iff.1 hs') hs.orderOf_x
  have hxQ : x ∈ T' ⊓ CxK x K := ⟨hxT', hs.x_mem_CxK⟩
  have hPD8 : IsD8 (T' ⊓ K) := ⟨eP⟩
  obtain ⟨z, hzP, hz1, hzz, hzc, hzu, hzsq⟩ := hPD8.exists_central_sq
  have hQinv : ∀ u ∈ T' ⊓ CxK x K, u * u = 1 → u = 1 ∨ u = x := by
    intro u hu huu
    by_cases hu1 : u = 1
    · exact Or.inl hu1
    · right
      have hmodel : ∀ v w : Multiplicative (ZMod 4), v * v = 1 → w * w = 1 → v ≠ 1 → w ≠ 1 →
          v = w := by decide
      have h1 : eQ ⟨u, hu⟩ * eQ ⟨u, hu⟩ = 1 := by
        rw [← map_mul]
        have : (⟨u, hu⟩ : ↥(T' ⊓ CxK x K)) * ⟨u, hu⟩ = 1 := Subtype.ext huu
        rw [this, map_one]
      have h2 : eQ ⟨x, hxQ⟩ * eQ ⟨x, hxQ⟩ = 1 := by
        rw [← map_mul]
        have : (⟨x, hxQ⟩ : ↥(T' ⊓ CxK x K)) * ⟨x, hxQ⟩ = 1 := Subtype.ext hxx
        rw [this, map_one]
      have h3 : eQ ⟨u, hu⟩ ≠ 1 := by
        intro h
        exact hu1 (congrArg Subtype.val (eQ.injective (h.trans (map_one eQ).symm)))
      have h4 : eQ ⟨x, hxQ⟩ ≠ 1 := by
        intro h
        exact hx1 (congrArg Subtype.val (eQ.injective (h.trans (map_one eQ).symm)))
      exact congrArg Subtype.val (eQ.injective (hmodel _ _ h1 h2 h3 h4))
  obtain ⟨q, hqQ, hqq⟩ : ∃ q ∈ T' ⊓ CxK x K, q * q = x := by
    refine ⟨((eQ.symm (Multiplicative.ofAdd (1 : ZMod 4)) : ↥(T' ⊓ CxK x K)) : G),
      (eQ.symm (Multiplicative.ofAdd (1 : ZMod 4))).2, ?_⟩
    have hmodel : ∀ u : Multiplicative (ZMod 4), u * u = 1 → u ≠ 1 →
        u = Multiplicative.ofAdd (1 : ZMod 4) * Multiplicative.ofAdd (1 : ZMod 4) := by decide
    have h1 : eQ ⟨x, hxQ⟩ * eQ ⟨x, hxQ⟩ = 1 := by
      rw [← map_mul]
      have : (⟨x, hxQ⟩ : ↥(T' ⊓ CxK x K)) * ⟨x, hxQ⟩ = 1 := Subtype.ext hxx
      rw [this, map_one]
    have h2 : eQ ⟨x, hxQ⟩ ≠ 1 := by
      intro h
      have : (⟨x, hxQ⟩ : ↥(T' ⊓ CxK x K)) = 1 := eQ.injective (h.trans (map_one eQ).symm)
      exact hx1 (congrArg Subtype.val this)
    have h3 := hmodel _ h1 h2
    have h4 : (⟨x, hxQ⟩ : ↥(T' ⊓ CxK x K)) = eQ.symm (Multiplicative.ofAdd (1 : ZMod 4)) *
        eQ.symm (Multiplicative.ofAdd (1 : ZMod 4)) := by
      apply eQ.injective
      rw [h3, map_mul, MulEquiv.apply_symm_apply]
    exact (congrArg Subtype.val h4).symm
  obtain ⟨p₀, hp₀, hqa⟩ := Subgroup.mem_map.1 (hα hqQ)
  have hqeq : q = a * p₀ * a⁻¹ := by
    rw [← hqa]; simp [MulAut.conj_apply]
  have hp0sq : p₀ * p₀ ≠ 1 := by
    intro h
    apply hx1
    rw [← hqq, hqeq]
    calc a * p₀ * a⁻¹ * (a * p₀ * a⁻¹) = a * (p₀ * p₀) * a⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hz0 : p₀ * p₀ = z := hzsq p₀ hp₀ hp0sq
  have hxz : a * z * a⁻¹ = x := by
    rw [← hz0, ← hqq, hqeq]
    group
  have hzT : ∀ t ∈ T', z * t = t * z := by
    intro t ht
    have ht' : t ∈ (T' ⊓ K) ⊔ (T' ⊓ K).map (MulAut.conj a).toMonoidHom := by
      rw [← hTeq]; exact ht
    obtain ⟨u, hu, u', hu', rfl⟩ := mem_sup_of_commute hcomm ht'
    have h1 : u * z = z * u := hzc u hu
    have h2 : z * u' = u' * z := hcomm z hzP u' hu'
    calc z * (u * u') = (z * u) * u' := by group
      _ = (u * z) * u' := by rw [h1]
      _ = u * (z * u') := by group
      _ = u * (u' * z) := by rw [h2]
      _ = (u * u') * z := by group
  have haa : a * a ∈ T' := by simpa [sq] using ha2
  have hxa : a * x * a⁻¹ = z := by
    have h1 := hzT (a * a) haa
    rw [← hxz]
    calc a * (a * z * a⁻¹) * a⁻¹ = (a * a) * z * (a * a)⁻¹ := by group
      _ = z := by rw [← h1]; group
  have hPaT : (T' ⊓ K).map (MulAut.conj a).toMonoidHom ≤ T' := by
    intro f hf
    have : f ∈ (T' ⊓ K) ⊔ (T' ⊓ K).map (MulAut.conj a).toMonoidHom := Subgroup.mem_sup_right hf
    rwa [← hTeq] at this
  have hpsiz : psi z = a7P 1 := by
    obtain ⟨i, hi⟩ := hpsiP z hzP
    have hcen : ∀ j : Fin 8, a7P i * a7P j = a7P j * a7P i := by
      intro j
      obtain ⟨u, hu, hj⟩ := hpsiPsurj j
      rw [← hi, ← hj, ← hpsimul z (hTC hzP.1) u (hTC hu.1), ← hpsimul u (hTC hu.1) z (hTC hzP.1),
        hzc u hu]
    rcases a7P_central_idx i hcen with h0 | h1
    · exfalso
      have h0' : psi z = 1 := by rw [hi, h0]; rfl
      have hodd : Odd (orderOf z) := hPsiD.ker_odd z hzP.2 h0'
      have h2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
      rw [h2] at hodd
      exact absurd hodd (by decide)
    · rw [hi, h1]
  have hpsix : psi x = 1 := (hpsiker x (hTC hxT')).2 hs.x_mem_CxK
  refine ⟨z, psi, ?_⟩
  exact
    { psiD := hPsiD
      psi_ker := hpsiker
      psi_P := hpsiP
      psi_P_surj := hpsiPsurj
      P_inv := hPinv
      T_le_C := hTC
      x_sq := hxx
      x_ne := hx1
      x_mem_T := hxT'
      psi_x := hpsix
      z_mem := hzP
      z_ne := hz1
      z_sq := hzz
      z_central := hzT
      psi_z := hpsiz
      hxz := hxz
      hxa := hxa
      haa := haa
      Pa_le := hPaT
      comm := hcomm
      disj := hdisj
      T_eq := hTeq
      Q_invol := hQinv }

end CFSG.GH74.GLS.Th2.AlphaStep
