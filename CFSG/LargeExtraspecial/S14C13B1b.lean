module

public import CFSG.LargeExtraspecial.S14C13B1
public import CFSG.LargeExtraspecial.S14C13Sym
public import CFSG.LargeExtraspecial.S14NQNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4

section Generic

variable {Y : Type} [Group Y] {M : Subgroup Y} {M0 : Subgroup M} {t0 : M0}

theorem nonempty_equiv_of_sym3 {N R : Subgroup Y} {Z : Type*} [Group Z] (res : R →* Z)
    (hres : ∀ r : R, res r = 1 ↔ (r : Y) ∈ N) {P : Type*} [Group P]
    {Φ : centralizer ({t0} : Set M0) →* Equiv.Perm (Fin 3) × P} (hΦs : Function.Surjective Φ)
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) = N)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set M0)))
    (hR0 : R ≤ Ct0 M0 ((t0 : M) : Y)) (hpre : ∀ c, (Φ c).1 = 1 → inclC M0 t0 c ∈ R)
    (hK1 : ∀ c ∈ R.comap (inclC M0 t0), (Φ c).1 = 1) : Nonempty (P ≃* res.range) := by
  have hΦ1 := map_eq_one_iff_of_ker hmap hΦk
  let χ : R.comap (inclC M0 t0) →* P :=
    ((MonoidHom.snd _ P).comp Φ).comp (R.comap (inclC M0 t0)).subtype
  have hχ : Function.Surjective χ := fun p => by
    obtain ⟨c, hc⟩ := hΦs (1, p)
    exact ⟨⟨c, hpre c (by rw [hc])⟩, by
      show (Φ c).2 = p
      rw [hc]⟩
  let ι : R.comap (inclC M0 t0) →* R :=
    { toFun := fun k => ⟨inclC M0 t0 k, k.2⟩
      map_one' := Subtype.ext (map_one (inclC M0 t0))
      map_mul' := fun a b => Subtype.ext (inclC_mul (a : centralizer ({t0} : Set M0)) b) }
  let ω : R.comap (inclC M0 t0) →* res.range := res.rangeRestrict.comp ι
  have hω : Function.Surjective ω := by
    rintro ⟨_, r, rfl⟩
    have hr' : (r : Y) ∈ (R.comap (inclC M0 t0)).map (inclC M0 t0) := by
      rw [map_comap_inclC hR0]
      exact r.2
    obtain ⟨k, hk, hkr⟩ := hr'
    exact ⟨⟨k, hk⟩, Subtype.ext (congrArg res (Subtype.ext hkr))⟩
  have hker : χ.ker = ω.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have hN := (hΦ1 k).mp (Prod.ext (hK1 k k.2) h)
      exact Subtype.ext ((hres (ι k)).mpr hN)
    · intro h
      have hN := (hres (ι k)).mp (congrArg Subtype.val h)
      exact congrArg Prod.snd ((hΦ1 k).mpr hN)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective χ hχ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective ω hω))⟩

theorem exists_noncomm_range {R : Subgroup Y} {Z : Type*} [Group Z] (res : R →* Z)
    (hperf : ⁅R, R⁆ = R) [Nontrivial res.range] : ∃ a b : res.range, a * b ≠ b * a := by
  by_contra hcon
  have hcon' : ∀ a b : res.range, a * b = b * a := fun a b => by
    by_contra h
    exact hcon ⟨a, b, h⟩
  have htop : ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ = ⊤ := by
    apply Subgroup.map_injective R.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map R.subtype, Subgroup.range_subtype, hperf]
  have hperfR : ⁅res.range, res.range⁆ = res.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, htop]
  have hcomm : ⁅res.range, res.range⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hcon' ⟨y, hy⟩ ⟨x, hx⟩)
  obtain ⟨x, hx⟩ := exists_ne (1 : res.range)
  apply hx
  have : (x : Z) ∈ (⊥ : Subgroup Z) := by
    rw [← hcomm, hperfR]
    exact x.2
  exact Subtype.ext ((mem_bot).mp this)

theorem le_Ct0_of_sym3 (hn : M0.Normal) {N R : Subgroup Y} {P : Type*} [Group P]
    {Φ : centralizer ({t0} : Set M0) →* Equiv.Perm (Fin 3) × P} (hΦs : Function.Surjective Φ)
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set M0))).map (inclC M0 t0) = N)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set M0)))
    (hR0 : R ≤ Ct0 M0 ((t0 : M) : Y)) (hpre : ∀ c, (Φ c).1 = 1 → inclC M0 t0 c ∈ R)
    (hK1 : ∀ c ∈ R.comap (inclC M0 t0), (Φ c).1 = 1)
    (hZ : ∀ p : P, (∀ q, p * q = q * p) → p = 1)
    (hNn : ∀ k ∈ M ⊓ centralizer ({((t0 : M) : Y)} : Set Y), ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hRn : ∀ k ∈ M ⊓ centralizer ({((t0 : M) : Y)} : Set Y), ∀ r ∈ R, k * r * k⁻¹ ∈ R)
    (hY : ∀ α β : centralizer ({t0} : Set M0), Φ α = (Equiv.swap 0 1, 1) →
      Φ β = (Equiv.swap 1 2, 1) → ∀ y ∈ M ⊓ centralizer ({((t0 : M) : Y)} : Set Y),
        y * inclC M0 t0 α * y⁻¹ * (inclC M0 t0 α)⁻¹ ∈ N →
        y * inclC M0 t0 β * y⁻¹ * (inclC M0 t0 β)⁻¹ ∈ N → y ∈ R) :
    M ⊓ centralizer ({((t0 : M) : Y)} : Set Y) ≤ Ct0 M0 ((t0 : M) : Y) := by
  intro x hx
  have hΦ1 := map_eq_one_iff_of_ker hmap hΦk
  obtain ⟨α, hα⟩ := hΦs (Equiv.swap 0 1, 1)
  obtain ⟨β, hβ⟩ := hΦs (Equiv.swap 1 2, 1)
  have hconj : ∀ a : centralizer ({t0} : Set M0), ∃ a' : centralizer ({t0} : Set M0),
      inclC M0 t0 a' = x * inclC M0 t0 a * x⁻¹ := fun a => by
    have hmem := conj_mem_Ct0 hn hx (inclC_mem_Ct0 a)
    rw [← range_inclC] at hmem
    exact hmem
  have hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N := hNn x hx
  have hxRi : ∀ r ∈ R, x⁻¹ * r * x⁻¹⁻¹ ∈ R := hRn x⁻¹ (inv_mem hx)
  have hback : ∀ a : centralizer ({t0} : Set M0),
      x * inclC M0 t0 a * x⁻¹ ∈ N → inclC M0 t0 a ∈ N := fun a h => by
    have := hNn x⁻¹ (inv_mem hx) _ h
    convert this using 1
    group
  have hsnd : ∀ (a a' : centralizer ({t0} : Set M0)) (σ : Equiv.Perm (Fin 3)),
      Φ a = (σ, 1) → inclC M0 t0 a' = x * inclC M0 t0 a * x⁻¹ → (Φ a').2 = 1 := by
    intro a a' σ ha ha'
    apply hZ
    intro q
    obtain ⟨k, hk⟩ := hΦs (1, q)
    have hkR := hpre k (by rw [hk])
    have h3 := hxN _ (comm_mem_of_map_eq hR0 hmap hΦk hK1 ha _ (hxRi _ hkR))
    have h4 : inclC M0 t0 (a' * k * a'⁻¹ * k⁻¹) ∈ N := by
      rw [inclC_mul, inclC_mul, inclC_mul, inclC_inv, inclC_inv, ha']
      convert h3 using 1
      group
    have h5 := congrArg Prod.snd ((hΦ1 _).mpr h4)
    simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, hk, Prod.snd_one] at h5
    calc (Φ a').2 * q = ((Φ a').2 * q * ((Φ a').2)⁻¹ * q⁻¹) * (q * (Φ a').2) := by group
      _ = q * (Φ a').2 := by rw [h5, one_mul]
  obtain ⟨α', hα'⟩ := hconj α
  obtain ⟨β', hβ'⟩ := hconj β
  have hα2 := hsnd α α' _ hα hα'
  have hβ2 := hsnd β β' _ hβ hβ'
  have hinv : ∀ (a a' : centralizer ({t0} : Set M0)) (σ : Equiv.Perm (Fin 3)),
      Φ a = (σ, 1) → σ * σ = 1 → σ ≠ 1 →
      inclC M0 t0 a' = x * inclC M0 t0 a * x⁻¹ → (Φ a').2 = 1 →
        (Φ a').1 * (Φ a').1 = 1 ∧ (Φ a').1 ≠ 1 := by
    intro a a' σ ha hσ hσ1 ha' ha2
    constructor
    · have h1 : inclC M0 t0 (a' * a') ∈ N := by
        rw [inclC_mul, ha']
        have := hxN _ (mul_self_mem_of_map_eq hmap hΦk ha hσ)
        convert this using 1
        group
      have h2 := (hΦ1 _).mpr h1
      rw [map_mul] at h2
      exact congrArg Prod.fst h2
    · intro h1
      have h2 := (hΦ1 a').mp (Prod.ext h1 ha2)
      rw [ha'] at h2
      have h4 := (hΦ1 a).mpr (hback a h2)
      rw [ha] at h4
      exact hσ1 (congrArg Prod.fst h4)
  obtain ⟨ha2, ha1⟩ := hinv α α' _ hα (by decide) (by decide) hα' hα2
  obtain ⟨hb2, hb1⟩ := hinv β β' _ hβ (by decide) (by decide) hβ' hβ2
  have hab : (Φ α').1 ≠ (Φ β').1 := by
    intro h
    have h1 : Φ (α' * β'⁻¹) = 1 := Prod.ext (by simp [h]) (by simp [hα2, hβ2])
    have h2 := (hΦ1 _).mp h1
    rw [inclC_mul, inclC_inv, hα', hβ'] at h2
    have h3 : inclC M0 t0 (α * β⁻¹) ∈ N := by
      refine hback _ ?_
      rw [inclC_mul, inclC_inv]
      convert h2 using 1
      group
    have h4 := (hΦ1 _).mpr h3
    rw [map_mul, map_inv, hα, hβ] at h4
    have h5 : Equiv.swap (0 : Fin 3) 1 * (Equiv.swap 1 2)⁻¹ = 1 := congrArg Prod.fst h4
    exact absurd h5 (by decide)
  obtain ⟨σ, hσa, hσb⟩ := exists_conj_swap_pair _ _ ha2 ha1 hb2 hb1 hab
  obtain ⟨c, hc⟩ := hΦs (σ, 1)
  have hyC : (inclC M0 t0 c)⁻¹ * x ∈ M ⊓ centralizer ({((t0 : M) : Y)} : Set Y) :=
    mul_mem (inv_mem (inclC_mem c)) hx
  have hcomm : ∀ (a a' : centralizer ({t0} : Set M0)) (τ : Equiv.Perm (Fin 3)),
      Φ a = (τ, 1) → inclC M0 t0 a' = x * inclC M0 t0 a * x⁻¹ →
      (Φ a').2 = 1 → σ * τ * σ⁻¹ = (Φ a').1 →
        ((inclC M0 t0 c)⁻¹ * x) * inclC M0 t0 a * ((inclC M0 t0 c)⁻¹ * x)⁻¹ *
          (inclC M0 t0 a)⁻¹ ∈ N := by
    intro a a' τ ha ha' ha2 hστ
    have h1 : Φ (c⁻¹ * a' * c * a⁻¹) = 1 := by
      simp only [map_mul, map_inv, hc, ha]
      ext
      · simp only [Prod.fst_mul, Prod.fst_inv, Prod.fst_one]
        rw [← hστ]
        group
      · simp only [Prod.snd_mul, Prod.snd_inv, Prod.snd_one, ha2]
        group
    have h2 := (hΦ1 _).mp h1
    rw [inclC_mul, inclC_mul, inclC_mul, inclC_inv, inclC_inv, ha'] at h2
    convert h2 using 1
    group
  have hyR := hY α β hα hβ _ hyC (hcomm α α' _ hα hα' hα2 hσa) (hcomm β β' _ hβ hβ' hβ2 hσb)
  have e : x = inclC M0 t0 c * ((inclC M0 t0 c)⁻¹ * x) := by group
  rw [e]
  exact mul_mem (inclC_mem_Ct0 c) (hR0 hyR)

end Generic

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem b1_equiv (haQ : g * S.z * g⁻¹ ∈ S.QG) {t0 : Mbar0 S}
    (hR0 : Rbar S g ((t0 : S.Mbar) : S.O) ≤ Ct0 (Mbar0 S) ((t0 : S.Mbar) : S.O))
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))).map (inclC (Mbar0 S) t0) =
      Nbar S g ((t0 : S.Mbar) : S.O))
    {P : Type} [Group P] (Φ : centralizer ({t0} : Set (Mbar0 S)) →* Equiv.Perm (Fin 3) × P)
    (hΦs : Function.Surjective Φ)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S))))
    (hpre : ∀ c, (Φ c).1 = 1 → inclC (Mbar0 S) t0 c ∈ Rbar S g ((t0 : S.Mbar) : S.O))
    (hK1 : ∀ c ∈ (Rbar S g ((t0 : S.Mbar) : S.O)).comap (inclC (Mbar0 S) t0), (Φ c).1 = 1) :
    Nonempty (P ≃* RmodN S g ((t0 : S.Mbar) : S.O)) :=
  (nonempty_equiv_of_sym3 (N := Nbar S g ((t0 : S.Mbar) : S.O))
    (resV haQ ((t0 : S.Mbar) : S.O)) (resV_eq_one_iff haQ) hΦs hmap hΦk hR0 hpre hK1).map
      fun e => e.trans (MulEquiv.subgroupCongr (range_resV haQ _))

theorem exists_noncomm_RmodN (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    (hperf : ⁅Rbar S g t, Rbar S g t⁆ = Rbar S g t) [Nontrivial (RmodN S g t)] :
    ∃ a b : RmodN S g t, a * b ≠ b * a := by
  have : Nontrivial (resV haQ t).range :=
    (MulEquiv.subgroupCongr (range_resV haQ t)).toEquiv.nontrivial
  obtain ⟨a, b, hab⟩ := exists_noncomm_range (resV haQ t) hperf
  exact ⟨MulEquiv.subgroupCongr (range_resV haQ t) a, MulEquiv.subgroupCongr (range_resV haQ t) b,
    by rw [← map_mul, ← map_mul, ne_eq, EmbeddingLike.apply_eq_iff_eq]; exact hab⟩

theorem eq_one_of_central_of_simple {A : Type*} [Group A] [IsSimpleGroup A]
    (hnc : ∃ a b : A, a * b ≠ b * a) {z : A} (hz : ∀ a, z * a = a * z) : z = 1 := by
  rcases (center A).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · have : z ∈ center A := mem_center_iff.mpr fun a => (hz a).symm
    rw [h] at this
    exact this
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ center A := h ▸ mem_top a
    exact hab ((mem_center_iff.mp ha b).symm)

theorem b1_Ct_le (hYb : Ybar13Stmt) [IsSimpleGroup G] {t0 : Mbar0 S}
    (hSt : Stage S g ((t0 : S.Mbar) : S.O))
    (hocc : Config.omegaPlus8b.Occurs S g ((t0 : S.Mbar) : S.O))
    (hext : IsExtraspecialPGroup 2 (Nbar S g ((t0 : S.Mbar) : S.O)))
    (h7 : Concl14_7 S g ((t0 : S.Mbar) : S.O))
    (hF : FCt S ((t0 : S.Mbar) : S.O) = Nbar S g ((t0 : S.Mbar) : S.O))
    (hR0 : Rbar S g ((t0 : S.Mbar) : S.O) ≤ Ct0 (Mbar0 S) ((t0 : S.Mbar) : S.O))
    (hmap : (timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S)))).map (inclC (Mbar0 S) t0) =
      Nbar S g ((t0 : S.Mbar) : S.O))
    {P : Type} [Group P] (Φ : centralizer ({t0} : Set (Mbar0 S)) →* Equiv.Perm (Fin 3) × P)
    (hΦs : Function.Surjective Φ)
    (hΦk : Φ.ker = timmesfeldFStar (centralizer ({t0} : Set (Mbar0 S))))
    (hpre : ∀ c, (Φ c).1 = 1 → inclC (Mbar0 S) t0 c ∈ Rbar S g ((t0 : S.Mbar) : S.O))
    (hK1 : ∀ c ∈ (Rbar S g ((t0 : S.Mbar) : S.O)).comap (inclC (Mbar0 S) t0), (Φ c).1 = 1)
    (hZ : ∀ p : P, (∀ q, p * q = q * p) → p = 1) :
    Ct S ((t0 : S.Mbar) : S.O) ≤ Ct0 (Mbar0 S) ((t0 : S.Mbar) : S.O) :=
  le_Ct0_of_sym3 (timmesfeldFStar_normal S.Mbar) hΦs hmap hΦk hR0 hpre hK1 hZ
    (fun _ hk _ hn => conj_mem_Nbar_of_mem_Ct hSt.hyp4.conj_mem hk hn)
    (fun _ hk _ hr => conj_mem_Rbar_of_mem_Ct hk hr)
    (fun _ _ hα hβ => b1_ybar hYb hSt hocc hext h7 hF hR0 hmap hΦk hK1 hα hβ)

end CFSG.LargeExtraspecial.S14
