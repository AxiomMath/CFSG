module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Layer
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62

open CFSG CFSG.LocalCores CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
open scoped commutatorElement
open CFSG.LocalAnalysis.RankThreeTheoremC (IsMaxTwoInvariantIn IsTwoInvariantIn)

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_normalizer_of_conj_mem {S : Subgroup Y} {g : Y} (h : ∀ s ∈ S, g * s * g⁻¹ ∈ S) :
    g ∈ normalizer (S : Set Y) := by
  have hsurj : Function.Surjective (fun s : S => (⟨g * s * g⁻¹, h s s.2⟩ : S)) := by
    apply Finite.surjective_of_injective
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (by simpa using this)
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  obtain ⟨s, hs⟩ := hsurj ⟨g * y * g⁻¹, hy⟩
  have h1 : g * (s : Y) * g⁻¹ = g * y * g⁻¹ := congrArg Subtype.val hs
  have hsy : (s : Y) = y := by simpa using h1
  exact hsy ▸ s.2

theorem mem_normalizer_sup' {A B : Subgroup Y} {g : Y} (hA : g ∈ normalizer (A : Set Y))
    (hB : g ∈ normalizer (B : Set Y)) : g ∈ normalizer ((A ⊔ B : Subgroup Y) : Set Y) := by
  have : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => Subgroup.mem_sup_left ((mem_normalizer_iff.mp hA a).mp ha))
      (fun b hb => Subgroup.mem_sup_right ((mem_normalizer_iff.mp hB b).mp hb))
  exact mem_normalizer_of_conj_mem fun s hs => this hs

theorem π_congr {hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥} (C : ComponentIndex Y) {x y : Y}
    (h : x = y) (hx : x ∈ layer Y) (hy : y ∈ layer Y) : π hZ C x hx = π hZ C y hy := by
  subst h
  rfl

theorem π_conj_fix {hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥} {t : Y} (C : ComponentIndex Y)
    (ht : cjComp t C = C) {x : Y} (hx : x ∈ layer Y) :
    π hZ C (t * x * t⁻¹) (conj_mem_layer t hx) = t * π hZ C x hx * t⁻¹ := by
  have h := π_conj (hZ := hZ) t C hx
  rw [ht] at h
  exact h

theorem π_commutator_fix {hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥} {t : Y}
    (C : ComponentIndex Y) (ht : cjComp t C = C) {g : Y} (hg : g ∈ layer Y)
    (hmem : ⁅t, g⁆ ∈ layer Y) : π hZ C ⁅t, g⁆ hmem = ⁅t, π hZ C g hg⁆ := by
  have e : ⁅t, g⁆ = (t * g * t⁻¹) * g⁻¹ := by rw [commutatorElement_def]
  rw [π_congr C e hmem (mul_mem (conj_mem_layer t hg) (inv_mem hg)),
    π_mul C (conj_mem_layer t hg) (inv_mem hg), π_conj_fix C ht hg, π_inv C hg,
    commutatorElement_def]

theorem fixes_components {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card (ComponentIndex Y) = p)
    {x : Y} (htrans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C')
    {T : Subgroup Y} (hT2 : IsPGroup 2 T) (hxT : x ∈ normalizer (T : Set Y)) :
    ∀ t ∈ T, ∀ C : ComponentIndex Y, cjComp t C = C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hT2.card_modEq_card_fixedPoints (ComponentIndex Y)
  rw [hcard] at hmod
  have hfp : Nonempty (MulAction.fixedPoints ↥T (ComponentIndex Y)) := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Nat.card_of_isEmpty, Nat.modEq_zero_iff_dvd] at hmod
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hmod).symm
  obtain ⟨⟨C₀, hC₀⟩⟩ := hfp
  intro t ht C
  obtain ⟨k, hk⟩ := htrans C₀ C
  have ht' : (x ^ k)⁻¹ * t * x ^ k ∈ T := by
    have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ (Subgroup.pow_mem _ hxT k)) t).mp ht
    simpa using this
  have hfix : cjComp ((x ^ k)⁻¹ * t * x ^ k) C₀ = C₀ := hC₀ ⟨_, ht'⟩
  calc cjComp t C = cjComp t (cjComp (x ^ k) C₀) := by rw [hk]
    _ = cjComp (t * x ^ k) C₀ := (cjComp_mul t (x ^ k) C₀).symm
    _ = cjComp (x ^ k * ((x ^ k)⁻¹ * t * x ^ k)) C₀ := by congr 1; group
    _ = cjComp (x ^ k) (cjComp ((x ^ k)⁻¹ * t * x ^ k) C₀) := cjComp_mul _ _ _
    _ = C := by rw [hfix, hk]

theorem π_ne_one (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥) {x z : Y} (hxz : x * z = z * x)
    (hz1 : z ≠ 1) (hzL : z ∈ layer Y)
    (htrans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C')
    (C : ComponentIndex Y) : π hZ C z hzL ≠ 1 := by
  intro h1
  have hC : z ∈ centralizer (C.1 : Set Y) := (π_eq_one_iff (hZ := hZ) C hzL).mp h1
  apply hz1
  refine eq_one_of_π_eq_one (hZ := hZ) hzL fun C' => ?_
  rw [π_eq_one_iff (hZ := hZ) C' hzL, mem_centralizer_iff]
  intro c' hc'
  obtain ⟨k, rfl⟩ := htrans C C'
  have hcomm : Commute (x ^ k) z := (show Commute x z from hxz).pow_left k
  have hc'' : (x ^ k)⁻¹ * c' * x ^ k ∈ C.1 := (mem_cjComp_iff (x ^ k) C).mp hc'
  have h2 : ((x ^ k)⁻¹ * c' * x ^ k) * z = z * ((x ^ k)⁻¹ * c' * x ^ k) :=
    mem_centralizer_iff.mp hC _ hc''
  have hc0 : Commute z ((x ^ k)⁻¹ * c' * x ^ k) := h2.symm
  have h3 : Commute z (x ^ k * ((x ^ k)⁻¹ * c' * x ^ k) * (x ^ k)⁻¹) :=
    (hcomm.symm.mul_right hc0).mul_right hcomm.symm.inv_right
  have e : c' = x ^ k * ((x ^ k)⁻¹ * c' * x ^ k) * (x ^ k)⁻¹ := by group
  rw [e]
  exact h3.eq.symm

theorem zcoord_mem_normalizer
    (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x z : Y} (hxz : x * z = z * x) (hzL : z ∈ layer Y)
    (hcard : Nat.card (ComponentIndex Y) = p)
    (htrans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C')
    {T : Subgroup Y} (hT : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) ⊤ T)
    (C₀ : ComponentIndex Y) : π hZ C₀ z hzL ∈ normalizer (T : Set Y) := by
  obtain ⟨⟨-, hT2, hBT⟩, hmax⟩ := hT
  have hxT : x ∈ normalizer (T : Set Y) := hBT (Subgroup.mem_sup_left (mem_zpowers x))
  have hzT : z ∈ normalizer (T : Set Y) := hBT (Subgroup.mem_sup_right (mem_zpowers z))
  have hfix := fixes_components hp hp2 hcard htrans hT2 hxT
  obtain ⟨zc, hzc⟩ : ∃ zc : ComponentIndex Y → Y, ∀ C, zc C = π hZ C z hzL :=
    ⟨fun C => π hZ C z hzL, fun C => rfl⟩
  have hzcC : ∀ C, zc C ∈ C.1 := fun C => by rw [hzc]; exact π_mem C z hzL
  obtain ⟨EC, hEC⟩ : ∃ EC : ComponentIndex Y → Subgroup Y,
      ∀ C, EC C = ⁅T, zpowers (zc C)⁆ := ⟨fun C => ⁅T, zpowers (zc C)⁆, fun C => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Subgroup Y, E = ⁅T, zpowers z⁆ := ⟨_, rfl⟩
  have hE_T : E ≤ T := by
    rw [hE]
    exact le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hzT)
  have hEC_le : ∀ C, EC C ≤ C.1 := by
    intro C
    rw [hEC, commutator_le]
    intro t ht g hg
    have hg' : g ∈ C.1 := zpowers_le.mpr (hzcC C) hg
    have h1 : t * g * t⁻¹ ∈ C.1 := by
      have := mem_cjComp_of_mem t C hg'
      rwa [hfix t ht C] at this
    rw [commutatorElement_def]
    exact mul_mem h1 (inv_mem hg')
  have hEC_2 : ∀ C, IsPGroup 2 (EC C) := by
    intro C
    let ρ : layer Y →* Y := C.1.subtype.comp (coord hZ C)
    have hρ : ∀ (y : Y) (hy : y ∈ layer Y), ρ ⟨y, hy⟩ = π hZ C y hy := fun y hy => rfl
    have hG2 : IsPGroup 2 ((E.subgroupOf (layer Y)).map ρ) :=
      ((hT2.to_le hE_T).comap_subtype).map ρ
    refine hG2.to_le ?_
    rw [hEC, commutator_le]
    intro t ht g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    have hzk : z ^ k ∈ layer Y := zpow_mem hzL k
    have hmem : ⁅t, z ^ k⁆ ∈ layer Y := by
      rw [commutatorElement_def]
      exact mul_mem (conj_mem_layer t hzk) (inv_mem hzk)
    have hEmem : ⁅t, z ^ k⁆ ∈ E := by
      rw [hE]
      exact commutator_mem_commutator ht (zpow_mem_zpowers z k)
    refine ⟨⟨⁅t, z ^ k⁆, hmem⟩, hEmem, ?_⟩
    rw [hρ _ hmem, π_commutator_fix C (hfix t ht C) hzk hmem, π_zpow C hzL k, hzc]
  have hEC_normT : ∀ C, T ≤ normalizer (EC C : Set Y) := by
    intro C
    rw [hEC]
    exact normalizer_commutator_ge_left T _
  have hzc_norm : ∀ C, zc C ∈ normalizer (EC C : Set Y) := by
    intro C
    rw [hEC]
    exact normalizer_commutator_ge_right T _ (mem_zpowers _)
  have hEC_z : ∀ C, z ∈ normalizer (EC C : Set Y) := by
    intro C
    refine mem_normalizer_of_conj_mem (fun e he => ?_)
    have heC : e ∈ C.1 := hEC_le C he
    rw [conj_eq_π (hZ := hZ) C hzL heC, ← hzc C]
    exact (mem_normalizer_iff.mp (hzc_norm C) e).mp he
  have hxzx : x * z * x⁻¹ = z := by rw [hxz]; group
  have hzc_x : ∀ C₁, x * zc C₁ * x⁻¹ = zc (cjComp x C₁) := by
    intro C₁
    have h := π_conj (hZ := hZ) x C₁ hzL
    rw [π_congr (hZ := hZ) (cjComp x C₁) hxzx (conj_mem_layer x hzL) hzL] at h
    simp only [hzc]
    exact h.symm
  have hx_EC : ∀ C₁, ∀ e ∈ EC C₁, x * e * x⁻¹ ∈ EC (cjComp x C₁) := by
    intro C₁
    have hle : EC C₁ ≤ (EC (cjComp x C₁)).comap (MulAut.conj x).toMonoidHom := by
      rw [hEC, commutator_le]
      intro t ht g hg
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
      show (MulAut.conj x).toMonoidHom ⁅t, zc C₁ ^ k⁆ ∈ EC (cjComp x C₁)
      have e1 : (MulAut.conj x).toMonoidHom ⁅t, zc C₁ ^ k⁆ =
          ⁅(MulAut.conj x).toMonoidHom t, ((MulAut.conj x).toMonoidHom (zc C₁)) ^ k⁆ := by
        rw [map_commutatorElement, map_zpow]
      rw [e1, hEC]
      refine commutator_mem_commutator ?_ ?_
      · exact (mem_normalizer_iff.mp hxT t).mp ht
      · have h2 : (MulAut.conj x).toMonoidHom (zc C₁) = zc (cjComp x C₁) := by
          simpa [MulAut.conj_apply] using hzc_x C₁
        rw [h2]
        exact zpow_mem_zpowers _ k
    intro e he
    exact hle he
  obtain ⟨Es, hEs⟩ : ∃ Es : Subgroup Y,
      ∀ e, e ∈ Es ↔ ∃ he : e ∈ layer Y, ∀ C, π hZ C e he ∈ EC C := by
    refine ⟨{ carrier := {e | ∃ he : e ∈ layer Y, ∀ C, π hZ C e he ∈ EC C}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun e => Iff.rfl⟩
    · rintro a b ⟨ha, hA⟩ ⟨hb, hB⟩
      refine ⟨mul_mem ha hb, fun C => ?_⟩
      rw [π_mul C ha hb]
      exact (EC C).mul_mem (hA C) (hB C)
    · exact ⟨one_mem _, fun C => by rw [π_one]; exact (EC C).one_mem⟩
    · rintro a ⟨ha, hA⟩
      refine ⟨inv_mem ha, fun C => ?_⟩
      rw [π_inv C ha]
      exact (EC C).inv_mem (hA C)
  have hEs_2 : IsPGroup 2 Es := by
    intro e
    obtain ⟨he, hEe⟩ := (hEs e).mp e.2
    have h1 : ∀ C, ∃ n : ℕ, (π hZ C e he) ^ 2 ^ n = 1 := fun C => by
      obtain ⟨n, hn⟩ := hEC_2 C ⟨_, hEe C⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    choose n hn using h1
    refine ⟨Finset.univ.sup n, Subtype.ext ?_⟩
    show (e : Y) ^ 2 ^ (Finset.univ.sup n) = 1
    refine eq_one_of_π_eq_one (hZ := hZ) (pow_mem he _) fun C => ?_
    rw [π_pow C he]
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (Finset.mem_univ C) : n C ≤
      Finset.univ.sup n)
    rw [hm, Nat.pow_add, pow_mul, hn C, one_pow]
  have hEs_T : T ≤ normalizer (Es : Set Y) := by
    intro t ht
    refine mem_normalizer_of_conj_mem (fun e he => ?_)
    obtain ⟨hel, hEe⟩ := (hEs e).mp he
    refine (hEs _).mpr ⟨conj_mem_layer t hel, fun C => ?_⟩
    rw [π_conj_fix C (hfix t ht C) hel]
    exact (mem_normalizer_iff.mp (hEC_normT C ht) _).mp (hEe C)
  have hEs_z : z ∈ normalizer (Es : Set Y) := by
    refine mem_normalizer_of_conj_mem (fun e he => ?_)
    obtain ⟨hel, hEe⟩ := (hEs e).mp he
    refine (hEs _).mpr ⟨conj_mem_layer z hel, fun C => ?_⟩
    have h1 : π hZ C (z * e * z⁻¹) (conj_mem_layer z hel) =
        π hZ C z hzL * π hZ C e hel * (π hZ C z hzL)⁻¹ := by
      rw [π_mul C (mul_mem hzL hel) (inv_mem hzL), π_mul C hzL hel, π_inv C hzL]
    rw [h1, ← hzc C]
    exact (mem_normalizer_iff.mp (hzc_norm C) _).mp (hEe C)
  have hEs_x : x ∈ normalizer (Es : Set Y) := by
    refine mem_normalizer_of_conj_mem (fun e he => ?_)
    obtain ⟨hel, hEe⟩ := (hEs e).mp he
    refine (hEs _).mpr ⟨conj_mem_layer x hel, fun C => ?_⟩
    have hC1 : cjComp x (cjComp x⁻¹ C) = C := by
      rw [← cjComp_mul, mul_inv_cancel, cjComp_one]
    have h := π_conj (hZ := hZ) x (cjComp x⁻¹ C) hel
    rw [hC1] at h
    rw [h]
    have := hx_EC (cjComp x⁻¹ C) _ (hEe (cjComp x⁻¹ C))
    rwa [hC1] at this
  have hQ2 : IsPGroup 2 (Es ⊔ T : Subgroup Y) := hEs_2.to_sup_of_normal_left' hT2 hEs_T
  have hxQ := mem_normalizer_sup' hEs_x hxT
  have hzQ := mem_normalizer_sup' hEs_z hzT
  have hBQ : zpowers x ⊔ zpowers z ≤ normalizer ((Es ⊔ T : Subgroup Y) : Set Y) :=
    sup_le (zpowers_le.mpr hxQ) (zpowers_le.mpr hzQ)
  have hQT : Es ⊔ T = T := hmax _ ⟨le_top, hQ2, hBQ⟩ le_sup_right
  have hEsT : Es ≤ T := le_sup_left.trans hQT.le
  have hECEs : EC C₀ ≤ Es := by
    intro e he
    have heC : e ∈ C₀.1 := hEC_le C₀ he
    have hel : e ∈ layer Y := component_le_layer C₀.2 heC
    refine (hEs e).mpr ⟨hel, fun C' => ?_⟩
    by_cases h : C' = C₀
    · subst h
      rw [π_of_mem C' heC]
      exact he
    · rw [π_of_mem_of_ne (Ne.symm h) heC]
      exact (EC C').one_mem
  have hcomm : ⁅T, zpowers (zc C₀)⁆ ≤ T := by
    rw [← hEC]
    exact (hECEs.trans hEsT)
  have := le_normalizer_iff_commutator_le_left.mpr hcomm (mem_zpowers (zc C₀))
  rwa [hzc] at this

theorem exists_elemAbelian_of_coords
    (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥) {p : ℕ} (hp : p.Prime) {z : Y} (hzp : z ^ p = 1)
    (hzL : z ∈ layer Y) (hne : ∀ C : ComponentIndex Y, π hZ C z hzL ≠ 1)
    {T : Subgroup Y} (hN : ∀ C : ComponentIndex Y, π hZ C z hzL ∈ normalizer (T : Set Y)) :
    ∃ W : Subgroup Y, IsElemAbelian p W ∧ Nat.card W = p ^ Nat.card (ComponentIndex Y) ∧
      W ≤ normalizer (T : Set Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzCp : ∀ C : ComponentIndex Y, (π hZ C z hzL) ^ p = 1 := fun C => by
    have h := π_pow (hZ := hZ) C hzL p
    rw [π_congr (hZ := hZ) C hzp (pow_mem hzL p) (one_mem _), π_one] at h
    exact h.symm
  have hord : ∀ C : ComponentIndex Y, orderOf (π hZ C z hzL) = p := fun C =>
    orderOf_eq_prime (hzCp C) (hne C)
  let zC : ∀ C : ComponentIndex Y, C.1 := fun C => ⟨π hZ C z hzL, π_mem C z hzL⟩
  have hzCord : ∀ C, orderOf (zC C) = p := fun C => by
    rw [← Subgroup.orderOf_coe]
    exact hord C
  have hzCp' : ∀ C, (zC C) ^ p = 1 := fun C => by
    have := pow_orderOf_eq_one (zC C)
    rwa [hzCord C] at this
  let S : Subgroup (∀ C : ComponentIndex Y, C.1) :=
    Subgroup.pi Set.univ (fun C => zpowers (zC C))
  let W : Subgroup Y := S.map (layerMul Y)
  have hinj : Function.Injective (layerMul Y) := layerMul_injective hZ
  have hS : ∀ f ∈ S, ∀ C, ∃ m : ℤ, zC C ^ m = f C := fun f hf C =>
    mem_zpowers_iff.mp ((Subgroup.mem_pi _).mp hf C (Set.mem_univ C))
  refine ⟨W, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_, ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    show (a : Y) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    funext C
    obtain ⟨m, hm⟩ := hS a' ha' C
    obtain ⟨n, hn⟩ := hS b' hb' C
    show a' C * b' C = b' C * a' C
    rw [← hm, ← hn]
    exact (Commute.zpow_zpow_self (zC C) m n).eq
  · rintro _ ⟨a', ha', rfl⟩
    rw [← map_pow]
    have : a' ^ p = 1 := by
      funext C
      obtain ⟨m, hm⟩ := hS a' ha' C
      show (a' C) ^ p = 1
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzCp' C, one_zpow]
    rw [this, map_one]
  · rw [Subgroup.card_map_of_injective hinj]
    have e : Nat.card S = Nat.card (∀ C : ComponentIndex Y, zpowers (zC C)) :=
      Nat.card_congr
        ⟨fun f C => ⟨f.1 C, (Subgroup.mem_pi _).mp f.2 C (Set.mem_univ C)⟩,
          fun g => ⟨fun C => g C, (Subgroup.mem_pi _).mpr fun C _ => (g C).2⟩,
          fun f => rfl, fun g => rfl⟩
    rw [e, Nat.card_pi]
    simp [Nat.card_zpowers, hzCord, Finset.prod_const, Nat.card_eq_fintype_card]
  · rintro _ ⟨a', ha', rfl⟩
    rw [layerMul_apply]
    refine Subgroup.noncommProd_mem _ _ fun C _ => ?_
    obtain ⟨m, hm⟩ := hS a' ha' C
    have h1 : ((a' C : C.1) : Y) = (π hZ C z hzL) ^ m := by
      rw [← hm]
      simp [zC]
    rw [h1]
    exact Subgroup.zpow_mem _ (hN C) m

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62
