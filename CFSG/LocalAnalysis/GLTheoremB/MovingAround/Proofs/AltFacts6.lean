module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs129
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1211
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltInputs2
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims139

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (le_normalizer_gLAPPrimeCoreOf
  card_gLAPPrimeCoreOf_coprime gLAPPrimeCoreOf_le mem_gLAPPrimeCoreOf_iff)
open Equiv
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section PermHom

variable {p n : ℕ} {K : Subgroup G}

@[expose] noncomputable def permHom (e : barOf p K ≃* alternatingGroup (Fin n)) : ↥K →* Perm (Fin n) :=
  (alternatingGroup (Fin n)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (GLAPPrimeCore p ↥K)))

theorem permHom_apply (e : barOf p K ≃* alternatingGroup (Fin n)) (x : ↥K) :
    permHom e x = ((e (QuotientGroup.mk x) : alternatingGroup (Fin n)) : Perm (Fin n)) := rfl

theorem permHom_mem (e : barOf p K ≃* alternatingGroup (Fin n)) (x : ↥K) :
    permHom e x ∈ alternatingGroup (Fin n) := (e (QuotientGroup.mk x)).2

theorem exists_permHom_eq (e : barOf p K ≃* alternatingGroup (Fin n)) {σ : Perm (Fin n)}
    (hσ : σ ∈ alternatingGroup (Fin n)) : ∃ x : ↥K, permHom e x = σ := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ, hσ⟩)
  refine ⟨y, ?_⟩
  rw [permHom_apply, hy, MulEquiv.apply_symm_apply]

theorem permHom_eq_one_iff (e : barOf p K ≃* alternatingGroup (Fin n)) (x : ↥K) :
    permHom e x = 1 ↔ x ∈ GLAPPrimeCore p ↥K := by
  rw [← QuotientGroup.eq_one_iff, permHom_apply]
  constructor
  · intro h
    have h' : e (QuotientGroup.mk x) = 1 := Subtype.ext h
    exact (map_eq_one_iff e e.injective).1 h'
  · intro h
    rw [h, map_one]
    rfl

theorem ker_permHom (e : barOf p K ≃* alternatingGroup (Fin n)) :
    (permHom e).ker = GLAPPrimeCore p ↥K := by
  ext x
  rw [MonoidHom.mem_ker, permHom_eq_one_iff]

end PermHom

section Generic

theorem eq_one_of_mem_core {p : ℕ} [hp : Fact p.Prime] {K : Subgroup G} {x : ↥K}
    (hx : x ∈ GLAPPrimeCore p ↥K) (hxp : x ^ p = 1) : x = 1 := by
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥K)) := CFSG.pPrimeCore_coprime_card
  have hzN : (⟨x, hx⟩ : ↥(GLAPPrimeCore p ↥K)) ^ p = 1 := Subtype.ext (by simpa using hxp)
  have hord1 : orderOf (⟨x, hx⟩ : ↥(GLAPPrimeCore p ↥K)) ∣ p := orderOf_dvd_of_pow_eq_one hzN
  have hord2 : orderOf (⟨x, hx⟩ : ↥(GLAPPrimeCore p ↥K)) ∣ Nat.card (GLAPPrimeCore p ↥K) :=
    orderOf_dvd_natCard _
  have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord1 hcop) hord2
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1)

theorem card_map_eq {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (H : Subgroup X)
    (hH : ∀ x ∈ H, f x = 1 → x = 1) : Nat.card (H.map f) = Nat.card H := by
  have hinj : Function.Injective (f.comp H.subtype) := by
    intro a b hab
    have h1 : f ((a : X)⁻¹ * b) = 1 := by
      rw [map_mul, map_inv]
      have : f a = f b := hab
      rw [this, inv_mul_cancel]
    have h2 := hH _ (H.mul_mem (H.inv_mem a.2) b.2) h1
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [h, MonoidHom.range_comp, Subgroup.range_subtype]

theorem card_pullback {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {H : Subgroup X}
    (hH : ∀ x ∈ H, f x = 1 → x = 1) {F : Subgroup Y} (hF : F ≤ H.map f) :
    Nat.card ↥(F.comap f ⊓ H) = Nat.card F := by
  have hmap : (F.comap f ⊓ H).map f = F := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_inf.1 hx).1
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hF hy
      exact ⟨x, Subgroup.mem_inf.2 ⟨hy, hx⟩, rfl⟩
  have h := card_map_eq f (F.comap f ⊓ H) fun x hx => hH x (Subgroup.mem_inf.1 hx).2
  rw [hmap] at h
  exact h.symm

theorem map_normalizer_le {K : Subgroup G} (X' : Subgroup ↥K) :
    (Subgroup.normalizer (X' : Set ↥K)).map K.subtype ≤
      Subgroup.normalizer ((X'.map K.subtype : Subgroup G) : Set G) ⊓ K :=
  le_inf (Subgroup.le_normalizer_map _) (Subgroup.map_subtype_le _)

theorem mem_normalizer_sup_of_comm {Y Z : Type} [Group Y] [Finite Y] [Group Z] {p : ℕ}
    [Fact p.Prime] (f : Y →* Z) (hf : f.ker = CFSG.pPrimeCore p Y) {Q : Subgroup Y}
    (hQ : IsPGroup p ↥Q) {y : Y} (hc : ∀ x ∈ Q, f y * f x = f x * f y) :
    y ∈ Subgroup.normalizer (Q : Set Y) ⊔ CFSG.pPrimeCore p Y := by
  apply Claims1211.mem_normalizer_sup_of_normalizes hQ
  have hN : (CFSG.pPrimeCore p Y ⊔ Q : Subgroup Y) = (Q.map f).comap f := by
    rw [Subgroup.comap_map_eq, hf, sup_comm]
  rw [hN, Subgroup.mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_comap, map_mul, map_inv]
  constructor
  · rintro ⟨x, hx, hxh⟩
    refine ⟨x, hx, ?_⟩
    rw [← hxh, hc x hx, mul_inv_cancel_right]
  · rintro ⟨x, hx, hxh⟩
    refine ⟨x, hx, ?_⟩
    have h2 : f h = (f y)⁻¹ * f x * f y := by rw [hxh]; group
    rw [h2, mul_assoc, ← hc x hx]
    group

end Generic

section I241

theorem core_le_iSup {p : ℕ} (hp : p.Prime) {K E : Subgroup G} (hEK : E ≤ K)
    (hE : IsElemAbelian p E) (hE2 : p ^ 2 ≤ Nat.card E) :
    GLAPPrimeCoreOf p K ≤
      ⨆ (X : Subgroup G) (_ : X ≤ E ∧ X ≠ ⊥), Subgroup.normalizer (X : Set G) ⊓ K := by
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity hp hE hE2
    (hEK.trans (le_normalizer_gLAPPrimeCoreOf p K)) (card_gLAPPrimeCoreOf_coprime p K)
  rw [← hgen]
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
  have hza : Subgroup.zpowers a ≤ E := Subgroup.zpowers_le.2 ha
  have hz1 : Subgroup.zpowers a ≠ ⊥ := by
    intro h
    apply ha1
    have h1 := Subgroup.mem_zpowers a
    rw [h] at h1
    exact (Subgroup.mem_bot).1 h1
  refine le_trans ?_ (le_iSup₂_of_le (Subgroup.zpowers a) ⟨hza, hz1⟩ le_rfl)
  intro x hx
  obtain ⟨hxO, hxC⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨?_, gLAPPrimeCoreOf_le p K hxO⟩
  have hxC' : x ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hxC
  exact Subgroup.centralizer_le_normalizer _ hxC'

theorem succ_mul_le_pow {p m : ℕ} (hp : 3 ≤ p) (hm : 2 ≤ m) : (m + 1) * p ≤ p ^ m := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
  have h1 : 2 * d + 1 ≤ p ^ d := (Lemma129e.three_pow_ge d).trans (Nat.pow_le_pow_left hp d)
  rw [pow_succ]
  exact Nat.mul_le_mul_right _ (by omega)

theorem input24_1K_holds : Lemma118T.Input24_1K := by
  intro G _ _ p n hp hp2 hpn hn2 K hK E hEK hE hEr
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  obtain ⟨e⟩ := hK
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set H := ⨆ (X : Subgroup G) (_ : X ≤ E ∧ X ≠ ⊥), Subgroup.normalizer (X : Set G) ⊓ K with hH
  have hHK : H ≤ K := iSup₂_le fun _ _ => inf_le_right
  have hEcard : Nat.card E = p ^ (n / p) := by
    rw [Lemma129.card_eq_pow_pRank hp hE, hEr]
  have hE2 : p ^ 2 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right hp.pos hn2
  have hO : GLAPPrimeCoreOf p K ≤ H := core_le_iSup hp hEK hE hE2
  refine le_antisymm hHK ?_
  set E' : Subgroup ↥K := E.subgroupOf K with hE'
  have hE'card : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  have hinj : ∀ x ∈ E', (permHom e) x = 1 → x = 1 := by
    intro x hx h1
    have hxO : x ∈ GLAPPrimeCore p ↥K := (permHom_eq_one_iff e x).1 h1
    have hxp : x ^ p = 1 := Subtype.ext (by simpa using hE.2 _ (Subgroup.mem_subgroupOf.1 hx))
    exact eq_one_of_mem_core hxO hxp
  set R : Subgroup (Perm (Fin n)) := E'.map (permHom e) with hR
  have hRcard : Nat.card R = p ^ (n / p) := by
    rw [hR, card_map_eq (permHom e) E' hinj, hE'card, hEcard]
  have hRp : IsPGroup p R := IsPGroup.of_card hRcard
  have hlt : n < p ^ (n / p) :=
    calc n < p * (n / p + 1) := Nat.lt_mul_div_succ n hp.pos
      _ = (n / p + 1) * p := mul_comm _ _
      _ ≤ p ^ (n / p) := succ_mul_le_pow hp3 hn2
  have hn3 : 3 ≤ n :=
    calc 3 ≤ 2 * p := by omega
      _ ≤ n / p * p := Nat.mul_le_mul_right p hn2
      _ ≤ n := Nat.div_mul_le_self n p
  have hcardn : Fintype.card (Fin n) = n := Fintype.card_fin n
  have horb : ∀ ω : Fin n, Nat.card (MulAction.orbit R ω) ≤ n := by
    intro ω
    calc Nat.card (MulAction.orbit R ω) ≤ Nat.card (Fin n) := Finite.card_subtype_le _
      _ = n := by rw [Nat.card_eq_fintype_card, hcardn]
  have hgen := Inputs129.perm_gen_le hp3 hRp (by rwa [hcardn]) (by rw [hcardn]; exact hn3)
    (m := n) (by omega) horb
  have hstep : ∀ F : {F : Subgroup (Perm (Fin n)) // F ≤ R ∧ Nat.card R ≤ n * Nat.card F},
      GL83.altOn (GL83.PiGen.fixSet F.1) ≤ (H.subgroupOf K).map (permHom e) := by
    rintro ⟨F, hFR, hFcard⟩ g hg
    rw [GL83.mem_altOn] at hg
    obtain ⟨hgA, hgfix⟩ := hg
    obtain ⟨k, hk⟩ := exists_permHom_eq e hgA
    set X' : Subgroup ↥K := F.comap (permHom e) ⊓ E' with hX'
    set X : Subgroup G := X'.map K.subtype with hX
    have hXE : X ≤ E := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hx).2
    have hX'card : Nat.card X' = Nat.card F := card_pullback (permHom e) hinj hFR
    have hXcard : Nat.card X = Nat.card F := by
      rw [hX, Subgroup.card_map_of_injective K.subtype_injective, hX'card]
    have hXne : X ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card X = 1 := by rw [hbot, Subgroup.card_bot]
      rw [hXcard] at h1
      rw [h1, mul_one, hRcard] at hFcard
      omega
    have hX'p : IsPGroup p X' := by
      have hle : X' ≤ E' := inf_le_right
      have hE'p : IsPGroup p E' := IsPGroup.of_card (by rw [hE'card, hEcard])
      exact hE'p.to_le hle
    have hstab : ∀ x, g x ∈ GL83.PiGen.fixSet F ↔ x ∈ GL83.PiGen.fixSet F := by
      intro x
      constructor
      · intro hgx
        by_contra hx
        rw [hgfix x hx] at hgx
        exact hx hgx
      · intro hx
        by_contra hgx
        have h1 := hgfix (g x) hgx
        rw [g.injective h1] at hgx
        exact hgx hx
    have hcommF : ∀ f ∈ F, f * g = g * f := by
      intro f hf
      ext x
      simp only [Perm.mul_apply]
      by_cases hx : x ∈ GL83.PiGen.fixSet F
      · rw [hx f hf, (hstab x).2 hx f hf]
      · have hfx : f x ∉ GL83.PiGen.fixSet F := by
          intro h
          have h1 : f (f x) = f x := h f hf
          rw [f.injective h1] at h
          exact hx h
        rw [hgfix x hx, hgfix (f x) hfx]
    have hc : ∀ x ∈ X', (permHom e) k * (permHom e) x = (permHom e) x * (permHom e) k := by
      intro x hx
      rw [hk]
      exact (hcommF _ (Subgroup.mem_inf.1 hx).1).symm
    have hmem := mem_normalizer_sup_of_comm (permHom e) (ker_permHom e) hX'p hc
    have hle : (Subgroup.normalizer (X' : Set ↥K) ⊔ CFSG.pPrimeCore p ↥K).map K.subtype ≤ H := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · exact (map_normalizer_le X').trans (le_iSup₂_of_le X ⟨hXE, hXne⟩ le_rfl)
      · exact hO
    exact ⟨k, Subgroup.mem_subgroupOf.2 (hle ⟨k, hmem, rfl⟩), hk⟩
  have hle : alternatingGroup (Fin n) ≤ (H.subgroupOf K).map (permHom e) := hgen.trans (iSup_le hstep)
  intro k hk
  obtain ⟨h, hh, hhk⟩ := hle (permHom_mem e ⟨k, hk⟩)
  have hO' : h⁻¹ * ⟨k, hk⟩ ∈ GLAPPrimeCore p ↥K := by
    rw [← permHom_eq_one_iff e, map_mul, map_inv, hhk, inv_mul_cancel]
  have h1 : ((h⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ H := hO ⟨_, hO', rfl⟩
  have h2 : (h : G) ∈ H := Subgroup.mem_subgroupOf.1 hh
  have h3 := H.mul_mem h2 h1
  simpa using h3

end I241

section Local

theorem le_normalizer_of_conj {D T : Subgroup G} (h : ∀ d ∈ D, ∀ t ∈ T, d * t * d⁻¹ ∈ T) :
    D ≤ Subgroup.normalizer (T : Set G) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨h d hd z, fun hz => ?_⟩
  have h1 := h d⁻¹ (D.inv_mem hd) _ hz
  simpa [mul_assoc] using h1

theorem exists_two_sub_normalized {p : ℕ} [hp : Fact p.Prime] (V D : Subgroup G)
    (hDN : D ≤ Subgroup.normalizer (V : Set G)) (hD : IsPGroup p ↥D) (hV : ¬ p ∣ Nat.card V)
    (h2 : 2 ∣ Nat.card V) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 ↥T ∧ D ≤ Subgroup.normalizer (T : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : ↥D →* MulAut ↥V := (V.normalizerMonoidHom).comp (Subgroup.inclusion hDN)
  letI : MulAction ↥D (Sylow 2 ↥V) := MulAction.compHom (Sylow 2 ↥V) ψ
  have hnd : ¬ p ∣ Nat.card (Sylow 2 ↥V) := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 ↥V) := inferInstance
    intro hd
    exact hV (hd.trans ((Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _)))
  obtain ⟨P, hP⟩ := hD.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥V) hnd
  have hfix : ∀ g : ↥D, g • P = P := fun g => MulAction.mem_fixedPoints.1 hP g
  have hconj : ∀ d ∈ D, ∀ t ∈ (P : Subgroup ↥V).map V.subtype,
      d * t * d⁻¹ ∈ (P : Subgroup ↥V).map V.subtype := by
    intro d hd t ht
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ht
    have hsub : (ψ ⟨d, hd⟩) • (P : Subgroup ↥V) = P := by
      have h1 : (ψ ⟨d, hd⟩) • P = P := hfix ⟨d, hd⟩
      have h2 := congrArg (fun S : Sylow 2 ↥V => (S : Subgroup ↥V)) h1
      simpa only [Sylow.pointwise_smul_def] using h2
    have hmem : (ψ ⟨d, hd⟩) y ∈ (ψ ⟨d, hd⟩) • (P : Subgroup ↥V) :=
      Subgroup.smul_mem_pointwise_smul y _ _ hy
    rw [hsub] at hmem
    exact ⟨(ψ ⟨d, hd⟩) y, hmem, rfl⟩
  refine ⟨(P : Subgroup ↥V).map V.subtype, ?_, P.isPGroup'.map _, le_normalizer_of_conj hconj⟩
  intro hbot
  have h2P : 2 ∣ Nat.card P := P.dvd_card_of_dvd_card h2
  have hc : Nat.card ((P : Subgroup ↥V).map V.subtype) = Nat.card P :=
    Subgroup.card_map_of_injective V.subtype_injective
  rw [hbot, Subgroup.card_bot] at hc
  rw [← hc] at h2P
  exact absurd (Nat.le_of_dvd one_pos h2P) (by norm_num)

theorem mem_setStab_of_mapsTo {Ω : Type} [Fintype Ω] [DecidableEq Ω] {S : Finset Ω}
    {c : Perm Ω} (h : ∀ z ∈ S, c z ∈ S) : c ∈ Inputs129.setStab (S : Set Ω) := by
  have hmap : S.map c.toEmbedding = S :=
    Finset.eq_of_subset_of_card_le (fun z hz => by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hz
      exact h w hw) (by rw [Finset.card_map])
  rw [Inputs129.mem_setStab]
  intro z
  constructor
  · intro hz
    exact h z hz
  · intro hz
    have hz' : c z ∈ S.map c.toEmbedding := by rw [hmap]; exact hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_map.1 hz'
    have hwz' : w = z := c.injective hwz
    rw [← hwz']
    exact hw

theorem conj_mem_kleinOn {α : Type} [Fintype α] [DecidableEq α] {Δ : Finset α} (h4 : Δ.card = 4)
    {c g : Perm α} (hc : ∀ i ∈ Δ, c i ∈ Δ) (hg : g ∈ Claims126.kleinOn Δ) :
    c * g * c⁻¹ ∈ Claims126.kleinOn Δ := by
  rw [Claims126.mem_kleinOn h4] at hg ⊢
  obtain ⟨hga, hg1⟩ := hg
  obtain ⟨hgA, hgs⟩ := Claims126.mem_altOn.1 hga
  refine ⟨Claims126.mem_altOn.2 ⟨alternatingGroup.normal.conj_mem g hgA c, ?_⟩, ?_⟩
  · rw [Equiv.Perm.support_conj]
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    exact hc j (hgs hj)
  · rcases hg1 with h | h
    · left
      rw [h, mul_one, mul_inv_cancel]
    · right
      rw [Equiv.Perm.cycleType_conj]
      exact h

theorem card_le_of_kleinOn {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {K : Subgroup G} {a : G}
    (e : barOf p K ≃* alternatingGroup (Fin n)) {Δ : Finset (Fin n)} (h4 : Δ.card = 4)
    {Y Q₂ : Subgroup G} (hYK : Y ≤ K)
    (hY : ∀ y (hy : y ∈ Y), ∀ i ∈ Δ, permHom e ⟨y, hYK hy⟩ i ∈ Δ)
    (hQ₂ : Q₂ ≤ centBar p (Cg a) K) (hD : IsElemAbelian p (Y ⊔ Q₂)) :
    Nat.card ↥(Y ⊔ Q₂) ≤ p ^ GLATwoLocalRank p G := by
  classical
  obtain ⟨V', hV'⟩ : ∃ V' : Subgroup ↥K, V' = (Claims126.kleinOn Δ).comap (permHom e) := ⟨_, rfl⟩
  have hmemV' : ∀ v : ↥K, v ∈ V' ↔ permHom e v ∈ Claims126.kleinOn Δ := fun v => by
    rw [hV', Subgroup.mem_comap]
  obtain ⟨V, hV⟩ : ∃ V : Subgroup G, V = V'.map K.subtype := ⟨_, rfl⟩
  have hVcard : Nat.card V = Nat.card V' := by
    rw [hV]
    exact Subgroup.card_map_of_injective K.subtype_injective
  have hmap : V'.map (permHom e) = Claims126.kleinOn Δ := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact (hmemV' v).1 hv
    · intro g hg
      have hgA : g ∈ alternatingGroup (Fin n) :=
        (Claims126.mem_altOn.1 ((Claims126.mem_kleinOn h4).1 hg).1).1
      obtain ⟨v, hv⟩ := exists_permHom_eq e hgA
      exact ⟨v, (hmemV' v).2 (by rw [hv]; exact hg), hv⟩
  have h2 : 2 ∣ Nat.card V := by
    have h1 : Nat.card (V'.map (permHom e)) ∣ Nat.card V' := Subgroup.card_map_dvd V' (permHom e)
    rw [hmap, Claims126.card_kleinOn h4] at h1
    rw [hVcard]
    exact (by norm_num : (2 : ℕ) ∣ 4).trans h1
  have hpV : ¬ p ∣ Nat.card V := by
    rw [hVcard]
    intro hd
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' p hd
    have hwo : orderOf (v : ↥K) = p := by rw [Subgroup.orderOf_coe, hv]
    have hwp : (v : ↥K) ^ p = 1 := by rw [← hwo]; exact pow_orderOf_eq_one _
    have hwV : permHom e (v : ↥K) ∈ Claims126.kleinOn Δ := (hmemV' _).1 v.2
    have hdvd4 : orderOf (permHom e (v : ↥K)) ∣ 4 := by
      have h1 := orderOf_dvd_natCard (⟨permHom e (v : ↥K), hwV⟩ : ↥(Claims126.kleinOn Δ))
      rwa [Subgroup.orderOf_mk, Claims126.card_kleinOn h4] at h1
    have hpw : permHom e (v : ↥K) ^ p = 1 := by rw [← map_pow, hwp, map_one]
    have h4p : Nat.Coprime 4 p := by
      have h := Nat.Coprime.pow_left 2 ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2))
      simpa using h
    have hord1 : orderOf (permHom e (v : ↥K)) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd4 h4p)
        (orderOf_dvd_of_pow_eq_one hpw)
    have hw1 : permHom e (v : ↥K) = 1 := orderOf_eq_one_iff.1 hord1
    have hv1 := eq_one_of_mem_core ((permHom_eq_one_iff e _).1 hw1) hwp
    rw [hv1, orderOf_one] at hwo
    exact hp.out.one_lt.ne hwo
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) := by
    apply le_normalizer_of_conj
    intro d hd t ht
    rw [hV] at ht ⊢
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 ht
    have hdK : d ∈ K := hYK hd
    refine ⟨⟨d, hdK⟩ * v * ⟨d, hdK⟩⁻¹, (hmemV' _).2 ?_, rfl⟩
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_kleinOn h4 (hY d hd) ((hmemV' v).1 hv)
  have hQN : Q₂ ≤ Subgroup.normalizer (V : Set G) := by
    apply le_normalizer_of_conj
    intro q hq t ht
    rw [hV] at ht ⊢
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨γ, hγ1, hγq⟩ := Lemma118T.exists_barAut_one_of_mem_centBar (hQ₂ hq)
    refine ⟨K.normalizerMonoidHom γ v, (hmemV' _).2 ?_, ?_⟩
    · rw [permHom_apply, Lemma118T.mk_conj_of_barAut_one hγ1 v, ← permHom_apply]
      exact (hmemV' v).1 hv
    · show ((K.normalizerMonoidHom γ v : ↥K) : G) = q * (v : G) * q⁻¹
      rw [Lemma118T.normalizerMonoidHom_val, hγq]
  obtain ⟨T, hT1, hT2, hTN⟩ :=
    exists_two_sub_normalized V (Y ⊔ Q₂) (sup_le hYN hQN) hD.isPGroup hpV h2
  exact GL83.PiGen.card_le_pow_twoLocalRank hD hT2 hT1 hTN

theorem not_isSolvable_of_isQuasisimple {X : Type*} [Group X] (hX : CFSG.Open.IsQuasisimple X) :
    ¬ Group.IsSolvable X := by
  intro hs
  obtain ⟨hperf, hsimp⟩ := hX
  have htop : ∀ k, derivedSeries X k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [derivedSeries_succ, ih, ← _root_.commutator_def]
      exact hperf
  obtain ⟨k, hk⟩ := hs.solvable
  have hbot : (⊤ : Subgroup X) = ⊥ := by rw [← htop k, hk]
  have hall : ∀ x : X, x = 1 := fun x => by
    have h1 : x ∈ (⊤ : Subgroup X) := Subgroup.mem_top x
    rw [hbot] at h1
    exact (Subgroup.mem_bot).1 h1
  haveI := hsimp.toNontrivial
  obtain ⟨u, w, huw⟩ := exists_pair_ne (X ⧸ Subgroup.center X)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
  rw [hall x, hall y] at huw
  exact huw rfl

theorem five_le_of_isQuasisimple {X : Type*} [Group X] {n : ℕ} (hX : CFSG.Open.IsQuasisimple X)
    (e : X ≃* alternatingGroup (Fin n)) : 5 ≤ n := by
  by_contra hn
  haveI : Group.IsSolvable (alternatingGroup (Fin n)) :=
    alternatingGroup.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  exact not_isSolvable_of_isQuasisimple hX
    (solvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)

theorem isQuasisimple_barOf_of_pComponent {p : ℕ} (hp : p.Prime) {X K : Subgroup G}
    (hK : GLAPComponent p X K) : CFSG.Open.IsQuasisimple (barOf p K) :=
  CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
    (quotEquivBarX hp hK.1 hK.2.1).symm hK.2.2.1.2.2

theorem input118Local_holds : Lemma118T.Input118Local := by
  intro G _ _ m p B M E A a K h n Q₁ Q₂ hn hpn hT
  have hp : p.Prime := h.standing.prime
  have hp2 : p ≠ 2 := h.standing.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨e⟩ := id hn
  have hn5 : 5 ≤ n := five_le_of_isQuasisimple (isQuasisimple_barOf_of_pComponent hp h.hK) e
  have hn4 : 4 ≤ n := by omega
  have hQ₂K : Q₂ ⊓ K = ⊥ := Lemma118T.inf_eq_bot_of_elemAb_le_centBar hn hn4 hT.Q₂C hT.Q₂ab
  have hdisj : ∀ Y : Subgroup G, Y ≤ Q₁ → Y ⊓ Q₂ = ⊥ := by
    intro Y hY
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzY, hzQ⟩ := Subgroup.mem_inf.1 hz
    have h1 : z ∈ Q₂ ⊓ K := Subgroup.mem_inf.2 ⟨hzQ, hT.Q₁K (hY hzY)⟩
    rwa [hQ₂K] at h1
  have hcard : ∀ Y : Subgroup G, Y ≤ Q₁ → Nat.card ↥(Y ⊔ Q₂) = Nat.card Y * Nat.card Q₂ :=
    fun Y hY => CFSG.HardMathSupport.Solomon.LocalBalance.card_sup_eq_mul_of_commute
      (fun y hy q hq => hT.comm y (hY hy) q hq) (hdisj Y hY)
  have hQab : IsElemAbelian p (Q₁ ⊔ Q₂) := by
    refine isElemAbelian_sup_of_commute hT.Q₁ab hT.Q₂ab ?_
    exact fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => (hT.comm x hx y hy).symm
  have key : ∀ (Y : Subgroup G) (hYQ : Y ≤ Q₁) (Δ : Finset (Fin n)), Δ.card = 4 →
      (∀ y (hy : y ∈ Y), ∀ i ∈ Δ, permHom e ⟨y, hT.Q₁K (hYQ hy)⟩ i ∈ Δ) →
      Nat.card Y * Nat.card Q₂ ≤ p ^ GLATwoLocalRank p G := by
    intro Y hYQ Δ hΔ hY
    rw [← hcard Y hYQ]
    exact card_le_of_kleinOn hp2 e hΔ (hYQ.trans hT.Q₁K) hY hT.Q₂C
      (hQab.mono (sup_le_sup_right hYQ _))
  have hrank : ∀ s : ℕ, Nat.card ↥(Q₁ ⊔ Q₂) ≤ p ^ s → CFSG.Open.pRank p (Q₁ ⊔ Q₂) ≤ s := by
    intro s hs
    rw [Lemma129.card_eq_pow_pRank hp hQab] at hs
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hs
  have hQ1card : Nat.card Q₁ = p ^ (n / p) := by
    rw [Lemma129.card_eq_pow_pRank hp hT.Q₁ab, hT.Q₁rk]
  have hinj : ∀ x ∈ Q₁.subgroupOf K, permHom e x = 1 → x = 1 := by
    intro x hx h1
    have hxO : x ∈ GLAPPrimeCore p ↥K := (permHom_eq_one_iff e x).1 h1
    have hxp : x ^ p = 1 :=
      Subtype.ext (by simpa using hT.Q₁ab.2 _ (Subgroup.mem_subgroupOf.1 hx))
    exact eq_one_of_mem_core hxO hxp
  have hRcard : Nat.card ((Q₁.subgroupOf K).map (permHom e)) = p ^ (n / p) := by
    rw [card_map_eq _ _ hinj, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.Q₁K).toEquiv,
      hQ1card]
  have hRab : IsElemAbelian p ((Q₁.subgroupOf K).map (permHom e)) :=
    AltInputs2.isElemAbelian_map_hom _ (hT.Q₁ab.subgroupOf K)
  obtain ⟨k, x, hk, hxR, hxc, hxd⟩ :=
    AltInputs2.exists_pcyc hp3 hRab (by rw [hRcard, Fintype.card_fin])
  rw [Fintype.card_fin] at hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  ·
    have hQ1one : Nat.card Q₁ = 1 := by rw [hQ1card, ← hk, hk0, pow_zero]
    obtain ⟨Δ, -, hΔ⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
      (n := 4) (by rw [Finset.card_univ, Fintype.card_fin]; exact hn4)
    have hb := key ⊥ bot_le Δ hΔ (by
      intro y hy i hi
      have hy1 : y = 1 := (Subgroup.mem_bot).1 hy
      subst hy1
      show permHom e 1 i ∈ Δ
      rw [map_one]
      exact hi)
    rw [Subgroup.card_bot, one_mul] at hb
    have hQle : Nat.card ↥(Q₁ ⊔ Q₂) ≤ p ^ GLATwoLocalRank p G := by
      rw [hcard Q₁ le_rfl, hQ1one, one_mul]
      exact hb
    refine ⟨hrank _ (hQle.trans (Nat.pow_le_pow_right hp.pos (Nat.le_succ _))), fun hp3' => ?_⟩
    have h1 := hrank _ hQle
    rw [hp3'] at h1
    exact h1
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hcl := AltInputs2.closure_pcyc hxc hxd
    have hRcl : Subgroup.closure (Set.range x) = (Q₁.subgroupOf K).map (permHom e) := by
      apply Subgroup.eq_of_le_of_card_ge
      · exact (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hxR i)
      · rw [hRcard, hcl.1, hk]
    have hsupp : ∀ i, (x i).support.card = p := fun i => (hxc i).2
    have hdisjS : ∀ i ∈ (Finset.univ : Finset (Fin (k' + 1))),
        ∀ j ∈ (Finset.univ : Finset (Fin (k' + 1))), i ≠ j →
          Disjoint (x i).support (x j).support := fun i _ j _ hij =>
      Equiv.Perm.disjoint_iff_disjoint_support.1 (hxd i j hij)
    have hU : (Finset.univ.biUnion fun i => (x i).support).card = (k' + 1) * p := by
      rw [Finset.card_biUnion hdisjS]
      simp [hsupp]
    have hlt : (k' + 1) * p < n := by
      have h1 : (k' + 1) * p ≤ n := by rw [hk]; exact Nat.div_mul_le_self n p
      have h2 : (k' + 1) * p ≠ n := by
        intro h
        apply hpn
        rw [← h]
        exact Dvd.intro_left _ rfl
      omega
    obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := Finset.univ.biUnion fun i => (x i).support) (t := (Finset.univ : Finset (Fin n)))
      (by rw [hU, Finset.card_univ, Fintype.card_fin]; exact hlt)
    have hωi : ∀ i, ω ∉ (x i).support := fun i hi =>
      hω (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hi⟩)
    set S₀ : Finset (Fin n) := insert ω (x 0).support with hS₀
    have hS₀card : S₀.card = p + 1 := by
      rw [hS₀, Finset.card_insert_of_notMem (hωi 0), hsupp 0]
    have hcl' := AltInputs2.closure_pcyc (x := fun j : Fin k' => x j.succ) (fun j => hxc _)
      (fun i j hij => hxd _ _ (fun h => hij (Fin.succ_injective _ h)))
    have hC'R : Subgroup.closure (Set.range fun j : Fin k' => x j.succ) ≤
        (Q₁.subgroupOf K).map (permHom e) :=
      (Subgroup.closure_le _).2 (by rintro _ ⟨j, rfl⟩; exact hxR _)
    have hC'fix : Subgroup.closure (Set.range fun j : Fin k' => x j.succ) ≤
        Inputs129.fixOut ((S₀ : Set (Fin n))ᶜ) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, Inputs129.mem_fixOut]
      intro z hz
      have hzS : z ∈ S₀ := by simpa using hz
      rw [hS₀, Finset.mem_insert] at hzS
      rcases hzS with rfl | hz0
      · exact Equiv.Perm.notMem_support.1 (hωi _)
      · rcases hxd 0 j.succ (Fin.succ_ne_zero j).symm z with h | h
        · exact absurd h (Equiv.Perm.mem_support.1 hz0)
        · exact h
    obtain ⟨W', hW'⟩ : ∃ W' : Subgroup ↥K, W' =
        (Subgroup.closure (Set.range fun j : Fin k' => x j.succ)).comap (permHom e) ⊓
          Q₁.subgroupOf K := ⟨_, rfl⟩
    have hW'card : Nat.card W' = p ^ k' := by
      rw [hW', card_pullback _ hinj hC'R, hcl'.1]
    have hWQ : W'.map K.subtype ≤ Q₁ := by
      rintro _ ⟨w, hw, rfl⟩
      rw [hW'] at hw
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hw).2
    have hWcard : Nat.card (W'.map K.subtype) = p ^ k' := by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hW'card]
    obtain ⟨Δ, hΔS, hΔ⟩ := Finset.exists_subset_card_eq (s := S₀) (n := 4)
      (by rw [hS₀card]; omega)
    have hb1 := key (W'.map K.subtype) hWQ Δ hΔ (by
      intro y hy i hi
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
      rw [hW'] at hw
      have hΦw := hC'fix (Subgroup.mem_inf.1 hw).1
      have hiS : i ∉ ((S₀ : Set (Fin n))ᶜ) := by simpa using hΔS hi
      show permHom e w i ∈ Δ
      rw [Inputs129.mem_fixOut.1 hΦw i hiS]
      exact hi)
    have hfirst : Nat.card ↥(Q₁ ⊔ Q₂) ≤ p ^ (GLATwoLocalRank p G + 1) := by
      calc Nat.card ↥(Q₁ ⊔ Q₂) = Nat.card Q₁ * Nat.card Q₂ := hcard Q₁ le_rfl
        _ = p * (Nat.card (W'.map K.subtype) * Nat.card Q₂) := by
          rw [hQ1card, ← hk, hWcard, pow_succ]
          ring
        _ ≤ p * p ^ GLATwoLocalRank p G := Nat.mul_le_mul_left _ hb1
        _ = p ^ (GLATwoLocalRank p G + 1) := by rw [pow_succ, mul_comm]
    have hRstab : (Q₁.subgroupOf K).map (permHom e) ≤ Inputs129.setStab (S₀ : Set (Fin n)) := by
      rw [← hRcl]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨i, rfl⟩
      apply mem_setStab_of_mapsTo
      intro z hz
      rw [hS₀, Finset.mem_insert] at hz ⊢
      rcases hz with rfl | hz
      · left
        exact Equiv.Perm.notMem_support.1 (hωi i)
      · right
        by_cases hi : i = 0
        · subst hi
          exact Equiv.Perm.apply_mem_support.2 hz
        · rcases hxd 0 i (Ne.symm hi) z with h | h
          · exact absurd h (Equiv.Perm.mem_support.1 hz)
          · rw [h]
            exact hz
    have hsecond : p = 3 → Nat.card ↥(Q₁ ⊔ Q₂) ≤ p ^ GLATwoLocalRank p G := by
      intro hp3'
      have hS₀4 : S₀.card = 4 := by rw [hS₀card, hp3']
      have hb2 := key Q₁ le_rfl S₀ hS₀4 (by
        intro y hy i hi
        have hmem : permHom e ⟨y, hT.Q₁K hy⟩ ∈ (Q₁.subgroupOf K).map (permHom e) :=
          ⟨⟨y, hT.Q₁K hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
        exact (Inputs129.mem_setStab.1 (hRstab hmem) i).1 hi)
      rw [hcard Q₁ le_rfl]
      exact hb2
    refine ⟨hrank _ hfirst, fun hp3' => ?_⟩
    have h1 := hrank _ (hsecond hp3')
    rw [hp3'] at h1
    exact h1

end Local

section Balance

theorem ne_bot_of_pComponent {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) : J ≠ ⊥ := by
  intro hbot
  have hq := isQuasisimple_barOf_of_pComponent hp hJ
  haveI := hq.2.toNontrivial
  obtain ⟨u, w, huw⟩ := exists_pair_ne (barOf p J ⧸ Subgroup.center (barOf p J))
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u'
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w'
  have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.1 (hbot.le x.2))
  have hy : y = 1 := Subtype.ext (Subgroup.mem_bot.1 (hbot.le y.2))
  rw [hx, hy] at huw
  exact huw rfl

theorem diag_iso_of_family {p : ℕ} (hp : p.Prime) {X : Subgroup G} {t : G} (htX : t ∈ X)
    (htp : t ^ p = 1) (ht1 : t ≠ 1) {J : Subgroup G}
    (hJ : GLAPComponent p (X ⊓ Subgroup.centralizer ({t} : Set G)) J)
    {𝒞 : Set (Subgroup G)} (h𝒞 : ∀ L ∈ 𝒞, GLAPComponent p X L) (hJK : J ≤ ⨆ L ∈ 𝒞, L)
    (hstab : ∀ L ∈ 𝒞, ∀ e ∈ Subgroup.zpowers t, GLBConj e L ∈ 𝒞)
    (htr : ∀ L ∈ 𝒞, ∀ L' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers t, GLBConj e L = L')
    {L : Subgroup G} (hL : L ∈ 𝒞)
    (hcase : GLBConj t L ≠ L ∨ CFSG.Yardstones.Md0ec50421ce4.CentMod p L t) :
    Nonempty (barOf p J ⧸ Subgroup.center (barOf p J) ≃*
      barOf p L ⧸ Subgroup.center (barOf p L)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  classical
  set F : ↥𝒞 → Subgroup G := fun i => (i : Subgroup G) with hF
  have hKeq : (⨆ L ∈ 𝒞, L) = ⨆ i, F i := by
    apply le_antisymm
    · exact iSup₂_le fun L hL => le_iSup_of_le ⟨L, hL⟩ le_rfl
    · exact iSup_le fun i => le_iSup₂_of_le i.1 i.2 le_rfl
  set K := ⨆ i, F i with hKdef
  have hJK' : J ≤ K := hKeq ▸ hJK
  have hFX : ∀ i, F i ≤ X := fun i => (h𝒞 i.1 i.2).1
  have hKX : K ≤ X := iSup_le hFX
  have hJt : J ≤ Subgroup.centralizer ({t} : Set G) := hJ.1.trans inf_le_right
  have hJ' : GLAPComponent p (K ⊓ Subgroup.centralizer ({t} : Set G)) J :=
    glaPComponent_of_le hp hJ (le_inf hJK' hJt) (inf_le_inf_right _ hKX)
  have hJX : J ≤ X := hJ'.1.trans (inf_le_left.trans hKX)
  have hconjK : ∀ e ∈ Subgroup.zpowers t, GLBConj e K ≤ K := by
    intro e he
    rw [hKdef, gLBConj_iSup_eq]
    exact iSup_le fun i => le_iSup_of_le ⟨GLBConj e i.1, hstab i.1 i.2 e he⟩ le_rfl
  have hxK : GLBConj t K = K := by
    refine le_antisymm (hconjK t (Subgroup.mem_zpowers t)) ?_
    have h1 := gLBConj_mono t (hconjK t⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)))
    rwa [gLBConj_gLBConj_inv] at h1
  have hxKn : t ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_iff_gLBConj_eq.2 hxK
  have htord : orderOf t = p := orderOf_eq_prime htp ht1
  have hxp : IsPGroup p (Subgroup.zpowers t) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, htord]
    exact ⟨1, (pow_one p).symm⟩
  set xb : ↥X ⧸ GLAPPrimeCore p ↥X := QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨t, htX⟩ with hxb
  have hxbp : xb ^ p = 1 := by
    rw [hxb, ← map_pow]
    have : (⟨t, htX⟩ : ↥X) ^ p = 1 := Subtype.ext (by simp [htp])
    rw [this, map_one]
  have hxb1 : xb ≠ 1 := by
    intro h1
    have hmem : (⟨t, htX⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := (QuotientGroup.eq_one_iff _).1 h1
    have hord : orderOf (⟨⟨t, htX⟩, hmem⟩ : ↥(GLAPPrimeCore p ↥X)) = p := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact htord
    have hdiv := orderOf_dvd_natCard (⟨⟨t, htX⟩, hmem⟩ : ↥(GLAPPrimeCore p ↥X))
    rw [hord] at hdiv
    exact not_dvd_card_pPrimeCore hp X hdiv
  have hxbord : orderOf xb = p := orderOf_eq_prime hxbp hxb1
  have hLc : ∀ i, IsComponentOf (barX p X (F i)) ⊤ := fun i => (h𝒞 i.1 i.2).2.2.1
  have hKbar : barX p X K = sSup (Set.range fun i => barX p X (F i)) := by
    rw [sSup_range]
    refine le_antisymm (barX_iSup_le_iSup F hFX) (iSup_le fun i => ?_)
    exact Lemma1311.barX_mono' p (le_iSup F i)
  have hxbK : xb ∈ Subgroup.normalizer ((barX p X K : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
      Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    rw [mem_normalizer_iff_gLBConj_eq, hxb, ← barX_gLBConj_eq p htX K, hxK]
  have hcomp : ∀ Y ∈ Set.range fun i => barX p X (F i), IsComponentOf Y (barX p X K) := by
    rintro Y ⟨a, rfl⟩
    have hle : barX p X (F a) ≤ barX p X K := Lemma1311.barX_mono' p (le_iSup F a)
    exact ⟨hle, isSubnormal_of_le_of_le (hLc a).2.1 hle le_top, (hLc a).2.2⟩
  have hcomm : ∀ Y ∈ Set.range (fun i => barX p X (F i)),
      ∀ Y' ∈ Set.range (fun i => barX p X (F i)), Y ≠ Y' → ∀ u ∈ Y, ∀ v ∈ Y', u * v = v * u := by
    rintro Y ⟨a, rfl⟩ Y' ⟨b, rfl⟩ hne u hu v hv
    have hc := Sec13e.commute_of_isComponentOf (hLc a) (hLc b) hne
    have hmem := Subgroup.commutator_mem_commutator hu hv
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hcase' : xb ∈ Subgroup.centralizer ((barX p X K : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X)) ∨
      ∀ Y ∈ Set.range (fun i => barX p X (F i)),
        xb ∉ Subgroup.normalizer (Y : Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
    rcases hcase with hnL | hcm
    ·
      right
      rintro Y ⟨i, rfl⟩ hn
      have h1 : GLBConj xb (barX p X (F i)) = barX p X (F i) := gLBConj_eq_of_mem_normalizer hn
      rw [hxb, ← barX_gLBConj_eq p htX (F i)] at h1
      have h2 : GLBConj t i.1 = i.1 :=
        glaPComponent_unique (h𝒞 _ (hstab i.1 i.2 t (Subgroup.mem_zpowers t))) (h𝒞 i.1 i.2) h1
      obtain ⟨e, he, heL⟩ := htr i.1 i.2 L hL
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      have hc : t ^ k * t = t * t ^ k := ((Commute.refl t).zpow_left k).eq
      apply hnL
      rw [← heL, gLBConj_gLBConj, hc, ← gLBConj_gLBConj, h2]
    ·
      left
      have htL : t ∈ Subgroup.normalizer (L : Set G) := hcm.1
      have hall : ∀ i, F i = L := by
        intro i
        obtain ⟨e, he, heL⟩ := htr L hL i.1 i.2
        rw [show F i = i.1 from rfl, ← heL]
        exact mem_normalizer_iff_gLBConj_eq.1 ((Subgroup.zpowers_le.2 htL) he)
      have hKL : K ≤ L := iSup_le fun i => (hall i).le
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyL : y ∈ barX p X L := Lemma1311.barX_mono' p hKL hy
      obtain ⟨⟨k, hkX⟩, hk, rfl⟩ := hyL
      have hkL : k ∈ L := Subgroup.mem_subgroupOf.1 hk
      have h1 : ⁅k, t⁆ ∈ (⁅L, Subgroup.zpowers t⁆ : Subgroup G) :=
        Subgroup.commutator_mem_commutator hkL (Subgroup.mem_zpowers t)
      have h2 : ⁅k, t⁆ ∈ GLAPPrimeCoreOf p X :=
        glaPPrimeCoreOf_le_of_isSubnormal hp (h𝒞 L hL).2.1 (hcm.2 h1)
      obtain ⟨hmX, h3⟩ := (mem_gLAPPrimeCoreOf_iff p X _).1 h2
      have h4 : ⁅(⟨k, hkX⟩ : ↥X), (⟨t, htX⟩ : ↥X)⁆ ∈ GLAPPrimeCore p ↥X := h3
      have h5 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⁅(⟨k, hkX⟩ : ↥X), (⟨t, htX⟩ : ↥X)⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).2 h4
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h5
      exact h5
  have hQ := Prop126b.glaPComponent_barX_inf_centralizer hp htX hKX hxKn hxp hJ'
  obtain ⟨Y, ⟨i, rfl⟩, ⟨e⟩⟩ := input18_3_diag_holds (↥X ⧸ GLAPPrimeCore p ↥X) p hp (barX p X K)
    (Set.range fun i => barX p X (F i)) xb hxbord hxbK hKbar hcomp hcomm hcase' (barX p X J) hQ
  have e1 : barOf p J ≃* barOf p (barX p X J) := Prop126b.barOfBarX hp hJX
  have e2 : barOf p (F i) ≃* ↥(barX p X (F i)) := quotEquivBarX hp (hFX i) (h𝒞 i.1 i.2).2.1
  obtain ⟨e', -, heL⟩ := htr i.1 i.2 L hL
  have e3 : barOf p (F i) ≃* barOf p L := by
    rw [← heL]
    exact conjQuotEquiv p e' i.1
  exact ⟨((Claims139.centerQuotCongr e1).trans e).trans
    ((Claims139.centerQuotCongr e2.symm).trans (Claims139.centerQuotCongr e3))⟩

theorem isAltType_of_center_quot {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hSchur : Prop1116Design.InputSchurAltComp) {X J L : Subgroup G}
    (hL : GLAPComponent p X L) (hJn : IsAltType n (barOf p J)) (hn : 8 ≤ n)
    (e : barOf p J ⧸ Subgroup.center (barOf p J) ≃* barOf p L ⧸ Subgroup.center (barOf p L)) :
    IsAltType n (barOf p L) := by
  obtain ⟨f⟩ := id hJn
  have hZJ : Subgroup.center (barOf p J) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    exact Lemma118T.eq_one_of_central_barOf J hJn (by omega) w
      (fun v => Subgroup.mem_center_iff.1 hw v)
  have hA : IsAltType n (barOf p L ⧸ Subgroup.center (barOf p L)) :=
    ⟨e.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZJ).trans
      (QuotientGroup.quotientBot.trans f))⟩
  rcases hSchur hp hp2 hL n hA with hZ | ⟨-, h67⟩
  · obtain ⟨g⟩ := hA
    exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans g⟩
  · omega

theorem altBalanceInput_of_inputs
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h1415 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), CFSG.LocalAnalysis.GLTheoremA.I1415At G p)
    (hSchur : Prop1116Design.InputSchurAltComp) : AltBalanceInput := by
  intro G _ _ m p B M E A h t J n htM htp ht1 hJM hJ hJn hn10
  have hp : p.Prime := h.standing.prime
  have hp2 : p ≠ 2 := h.standing.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hMK : CFSG.Open.IsKGroup ↥M :=
    h.standing.kProper.isKGroup M (isTwoLocal_ne_top h.standing h.pre.1.1)
  have hJM' : GLAPComponent p (M ⊓ Subgroup.centralizer ({t} : Set G)) J :=
    glaPComponent_of_le hp hJ (le_inf hJM hJ.1) inf_le_right
  have hcent : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨𝒞, h𝒞, h𝒞eq, h𝒞st, h𝒞tr⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.input18_3_4_of_schreier hS G M hMK p hp
      (Subgroup.zpowers t) (Subgroup.zpowers_le.2 htM) (CFSG.Open.isElemAbelian_zpowers htp) J
      (by rw [hcent]; exact hJM')
  have hJle : J ≤ ⨆ L ∈ 𝒞, L := by
    rw [h𝒞eq]
    refine le_trans ?_ (le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) le_rfl)
    rw [gLBConj_one]
  obtain ⟨L, hL⟩ : ∃ L, L ∈ 𝒞 := by
    by_contra hcon
    have hbot : (⨆ L ∈ 𝒞, L) = ⊥ := iSup₂_eq_bot.2 fun L hL => absurd ⟨L, hL⟩ hcon
    rw [hbot] at hJle
    exact ne_bot_of_pComponent hp hJ (le_bot_iff.1 hJle)
  by_cases hnorm : GLBConj t L = L ∧ ¬ CFSG.Yardstones.Md0ec50421ce4.CentMod p L t
  ·
    obtain ⟨htL, hc⟩ := hnorm
    have htN : t ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_gLBConj_eq.2 htL
    have hall : ∀ L' ∈ 𝒞, L' = L := by
      intro L' hL'
      obtain ⟨e, he, heL⟩ := h𝒞tr L hL L' hL'
      rw [← heL]
      exact mem_normalizer_iff_gLBConj_eq.1 ((Subgroup.zpowers_le.2 htN) he)
    have hJL : J ≤ L := hJle.trans (iSup₂_le fun L' hL' => (hall L' hL').le)
    have hJL' : GLAPComponent p (L ⊓ Subgroup.centralizer ({t} : Set G)) J :=
      glaPComponent_of_le hp hJM' (le_inf hJL hJ.1) (inf_le_inf_right _ (h𝒞 L hL).1)
    obtain ⟨k, hk, hkL⟩ :=
      h1415 G p hp hp2 M L J t n hMK (h𝒞 L hL) htN htp hc hJL' (by omega) hJn
    exact ⟨L, n + k * p, h𝒞 L hL, hkL, by omega⟩
  ·
    have hcase : GLBConj t L ≠ L ∨ CFSG.Yardstones.Md0ec50421ce4.CentMod p L t :=
      (not_and_or.1 hnorm).imp id not_not.1
    obtain ⟨e⟩ := diag_iso_of_family hp htM htp ht1 hJM' h𝒞 hJle h𝒞st h𝒞tr hL hcase
    exact ⟨L, n, h𝒞 L hL, isAltType_of_center_quot hp hp2 hSchur (h𝒞 L hL) hJn (by omega) e,
      le_rfl⟩

end Balance

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts6
