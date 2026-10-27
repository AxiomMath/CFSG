module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.BorelTitsConstrained
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LieType.BorelTits CFSG.HardMathSupport.Timmesfeld.Coordinator
open scoped commutatorElement

theorem lieQConstrained_inner {q : ℕ} (hL : LieQConstrained q) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) (hChev : IsChevOfChar q S)
    {Q : Subgroup S} (hQ : Q ≠ ⊥) (hQp : IsPGroup q ↥Q) :
    ∀ x ∈ Subgroup.normalizer (Q : Set S),
      (∀ r ∈ pCoreOf q (Subgroup.normalizer (Q : Set S)), x * r = r * x) →
      x ∈ pCoreOf q (Subgroup.normalizer (Q : Set S)) := by
  have hsimple : IsSimpleGroup ↥(⊤ : Subgroup S) := Subgroup.topEquiv.isSimpleGroup_congr.2 hS
  obtain ⟨a, b, hab⟩ := hnab
  have hnonab : ∃ a b : ↥(⊤ : Subgroup S), a * b ≠ b * a :=
    ⟨Subgroup.topEquiv.symm a, Subgroup.topEquiv.symm b, fun h => hab (by
      have := congrArg Subgroup.topEquiv h
      simpa using this)⟩
  have hChevTop : IsChevOfChar q ↥(⊤ : Subgroup S) := by
    obtain ⟨d, hd, ⟨e⟩⟩ := hChev
    exact ⟨d, hd, ⟨Subgroup.topEquiv.trans e⟩⟩
  have hcent : Subgroup.centralizer ((⊤ : Subgroup S) : Set S) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  intro x hx hc
  exact hL S ⊤ inferInstance hsimple hnonab hChevTop hcent Q le_top hQ hQp x hx hc

theorem conj_injective_of_simple {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  rw [← MonoidHom.ker_eq_bot_iff, ← hZ]
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := congrArg (fun φ : MulAut S => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact (h g).symm

theorem lieQConstrained_aut {q : ℕ} [Fact q.Prime] (hL : LieQConstrained q) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) (hChev : IsChevOfChar q S)
    (β : MulAut S) {m : ℕ} (hm : Nat.Coprime m q) (hβ : β ^ m = 1)
    {Q : Subgroup S} (hQ : Q ≠ ⊥) (hQp : IsPGroup q ↥Q) (hQfix : ∀ x ∈ Q, β x = x)
    (hfix : ∀ s ∈ pCoreOf q (Subgroup.normalizer (Q : Set S)), β s = s) : β = 1 := by
  classical
  have hinj := conj_injective_of_simple hS hnab
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  set C : Subgroup (MulAut S) := (MulAut.conj : S →* MulAut S).range with hC
  haveI hCn : C.Normal := ⟨fun n hn g => by
    obtain ⟨s, rfl⟩ := hn
    refine ⟨g s, ?_⟩
    ext x
    simp [MulAut.conj_apply]⟩
  set X : Subgroup (MulAut S) := C ⊔ Subgroup.zpowers β with hX
  have hCX : C ≤ X := le_sup_left
  have hβX : β ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers β)
  let ι : S →* ↥X := (MulAut.conj : S →* MulAut S).codRestrict X (fun s => hCX ⟨s, rfl⟩)
  have hιc : ∀ s, ((ι s : ↥X) : MulAut S) = MulAut.conj s := fun s => rfl
  have hι : Function.Injective ι := fun a b h => hinj (by
    have := congrArg Subtype.val h
    simpa [hιc] using this)
  let h : ↥X := ⟨β, hβX⟩
  have hconj : ∀ (g : ↥X) (s : S), g * ι s * g⁻¹ = ι ((g : MulAut S) s) := by
    intro g s
    apply Subtype.ext
    show (g : MulAut S) * MulAut.conj s * (g : MulAut S)⁻¹ = MulAut.conj ((g : MulAut S) s)
    ext x
    simp [MulAut.conj_apply]
  have hnormal : ι.range.Normal := ⟨fun n hn g => by
    obtain ⟨s, rfl⟩ := hn
    rw [hconj]
    exact ⟨_, rfl⟩⟩
  let e : S ≃* ι.range := MonoidHom.ofInjective hι
  have hsimple : IsSimpleGroup ↥ι.range := e.isSimpleGroup_congr.1 hS
  have hnab' : ∃ a b : ↥ι.range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul]; exact h'))⟩
  have hChev' : IsChevOfChar q ↥ι.range := by
    obtain ⟨d, hd, ⟨f⟩⟩ := hChev
    exact ⟨d, hd, ⟨e.symm.trans f⟩⟩
  have hcent : Subgroup.centralizer (ι.range : Set ↥X) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hcomm : ∀ s : S, g * ι s = ι s * g := fun s =>
      (Subgroup.mem_centralizer_iff.1 hg (ι s) ⟨s, rfl⟩).symm
    have hfixg : ∀ s : S, (g : MulAut S) s = s := fun s => hι (by
      rw [← hconj g s, hcomm s, mul_inv_cancel_right])
    exact Subtype.ext (MulEquiv.ext hfixg)
  have hQle : Q.map ι ≤ ι.range := Subgroup.map_le_range ι Q
  have hQne : Q.map ι ≠ ⊥ := fun hb => hQ ((Subgroup.map_eq_bot_iff_of_injective Q hι).1 hb)
  have hQpH : IsPGroup q ↥(Q.map ι) := hQp.map ι
  have hinvfix : ∀ x ∈ Q, ((h⁻¹ : ↥X) : MulAut S) x = x := by
    intro x hx
    have h0 : ((h⁻¹ : ↥X) : MulAut S) = β⁻¹ := rfl
    rw [h0]
    calc β⁻¹ x = β⁻¹ (β x) := by rw [hQfix x hx]
      _ = x := MulAut.inv_apply_self S β x
  have hhn : h ∈ Subgroup.normalizer ((Q.map ι : Subgroup ↥X) : Set ↥X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : ((h : ↥X) : MulAut S) x = x := hQfix x hx
      rw [hconj, hx']
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      have h1 : y = h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ := by group
      rw [h1, ← hxy, hconj h⁻¹ x, hinvfix x hx]
      exact ⟨x, hx, rfl⟩
  have hh1 : h ^ m = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hβ)
  have hrange_sup : ∀ g : ↥X, ∃ n ∈ ι.range, ∃ j : ℤ, g = n * h ^ j := by
    intro g
    have hg : (g : MulAut S) ∈ C ⊔ Subgroup.zpowers β := g.2
    obtain ⟨c, hc, z, hz, hcz⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    obtain ⟨s, rfl⟩ := hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine ⟨ι s, ⟨s, rfl⟩, j, ?_⟩
    apply Subtype.ext
    show (g : MulAut S) = MulAut.conj s * β ^ j
    exact hcz.symm
  have hpowC : ∀ g : ↥X, g ^ m ∈ ι.range := by
    intro g
    obtain ⟨n, hn, j, rfl⟩ := hrange_sup g
    haveI := hnormal
    have hmk : (QuotientGroup.mk (n * h ^ j) : ↥X ⧸ ι.range) = (QuotientGroup.mk h) ^ j := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul, QuotientGroup.mk_zpow]
    have h1 : (QuotientGroup.mk ((n * h ^ j) ^ m) : ↥X ⧸ ι.range) = 1 := by
      rw [QuotientGroup.mk_pow, hmk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        ← QuotientGroup.mk_pow, hh1]
      simp
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hq_range : ∀ r ∈ pCoreOf q (Subgroup.normalizer ((Q.map ι : Subgroup ↥X) : Set ↥X)),
      r ∈ ι.range := by
    intro r hr
    haveI := hnormal
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup q
      (Subgroup.normalizer ((Q.map ι : Subgroup ↥X) : Set ↥X))) ⟨r, hr⟩
    have hrk : r ^ q ^ k = 1 := by
      have h0 := congrArg Subtype.val hk
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h0
      exact h0
    have h1 : (QuotientGroup.mk r : ↥X ⧸ ι.range) ^ q ^ k = 1 := by
      rw [← QuotientGroup.mk_pow, hrk]; rfl
    have h2 : (QuotientGroup.mk r : ↥X ⧸ ι.range) ^ m = 1 := by
      rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).2 (hpowC r)
    have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [show Nat.gcd (q ^ k) m = 1 from Nat.Coprime.pow_left k hm.symm, Nat.dvd_one,
      orderOf_eq_one_iff] at h3
    exact (QuotientGroup.eq_one_iff r).1 h3
  have hcomm : ∀ r ∈ pCoreOf q (Subgroup.normalizer ((Q.map ι : Subgroup ↥X) : Set ↥X)),
      h * r = r * h := by
    intro r hr
    obtain ⟨s, rfl⟩ := hq_range r hr
    set N_H : Subgroup ↥X := Subgroup.normalizer ((Q.map ι : Subgroup ↥X) : Set ↥X) with hNH
    have hs : s ∈ pCoreOf q (Subgroup.normalizer (Q : Set S)) := by
      let P : Subgroup S := (pCoreOf q N_H).comap ι
      have hPN : P ≤ Subgroup.normalizer (Q : Set S) := by
        intro p hp
        have hp' : ι p ∈ N_H := pCoreOf_le q N_H hp
        rw [hNH, Subgroup.mem_normalizer_iff] at hp'
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h1 := hp' (ι y)
        have hmul : ι p * ι y * (ι p)⁻¹ = ι (p * y * p⁻¹) := by simp [map_mul, map_inv]
        rw [hmul, Subgroup.mem_map_iff_mem hι, Subgroup.mem_map_iff_mem hι] at h1
        exact h1
      have hPnorm : (P.subgroupOf (Subgroup.normalizer (Q : Set S))).Normal := by
        refine ⟨fun x hx g => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        have hg : ι (g : S) ∈ N_H := Subgroup.le_normalizer_map ι ⟨g, g.2, rfl⟩
        have h1 := le_normalizer_pCoreOf q N_H hg
        have h2 := (Subgroup.mem_normalizer_iff.1 h1 (ι (x : S))).1 hx
        show ι ((g : S) * (x : S) * (g : S)⁻¹) ∈ pCoreOf q N_H
        simpa [map_mul, map_inv] using h2
      have hPp : IsPGroup q ↥P := by
        intro x
        obtain ⟨k, hk⟩ := (pCoreOf_isPGroup q N_H) ⟨ι (x : S), x.2⟩
        refine ⟨k, Subtype.ext (hι ?_)⟩
        have := congrArg Subtype.val hk
        simpa [map_pow] using this
      exact le_pCoreOf q hPN hPnorm hPp hr
    have h1 := hconj h s
    rw [show ((h : ↥X) : MulAut S) s = s from hfix s hs] at h1
    calc h * ι s = h * ι s * h⁻¹ * h := by group
      _ = ι s * h := by rw [h1]
  have hmem := hL ↥X ι.range hnormal hsimple hnab' hChev' hcent (Q.map ι) hQle hQne hQpH h hhn
    hcomm
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup q
    (Subgroup.normalizer ((Q.map ι : Subgroup ↥X) : Set ↥X))) ⟨h, hmem⟩
  have hhk : h ^ q ^ k = 1 := by
    have h0 := congrArg Subtype.val hk
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h0
    exact h0
  have hβk : β ^ q ^ k = 1 := by simpa using congrArg Subtype.val hhk
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hβk) (orderOf_dvd_of_pow_eq_one hβ)
  rw [show Nat.gcd (q ^ k) m = 1 from Nat.Coprime.pow_left k hm.symm, Nat.dvd_one,
    orderOf_eq_one_iff] at h1
  exact h1

section KLevel

variable {G : Type} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]

theorem pCoreOf_normalizer_map_eq (hZ : Nat.Coprime (Nat.card (Subgroup.center G)) q)
    {Q : Subgroup G} (hQp : IsPGroup q ↥Q) :
    pCoreOf q (Subgroup.normalizer ((Q.map (QuotientGroup.mk' (Subgroup.center G)) :
        Subgroup (G ⧸ Subgroup.center G)) : Set (G ⧸ Subgroup.center G))) =
      (pCoreOf q (Subgroup.normalizer (Q : Set G))).map (QuotientGroup.mk' (Subgroup.center G)) := by
  have hN := normalizer_eq_comap_normalizer_map (Subgroup.center G) le_rfl hZ hQp
  have hsurj : Function.Surjective (QuotientGroup.mk' (Subgroup.center G)) :=
    QuotientGroup.mk'_surjective _
  apply le_antisymm
  · have h1 := pCoreOf_le_map_pCoreOf_comap (r := q) (Subgroup.center G) le_rfl hZ
      (Subgroup.normalizer ((Q.map (QuotientGroup.mk' (Subgroup.center G)) :
        Subgroup (G ⧸ Subgroup.center G)) : Set (G ⧸ Subgroup.center G)))
    rw [← hN] at h1
    exact h1
  · have h2 := map_pCoreOf_le (r := q) (QuotientGroup.mk' (Subgroup.center G))
      (Subgroup.normalizer (Q : Set G))
    have h3 : (Subgroup.normalizer (Q : Set G)).map (QuotientGroup.mk' (Subgroup.center G)) =
        Subgroup.normalizer ((Q.map (QuotientGroup.mk' (Subgroup.center G)) :
          Subgroup (G ⧸ Subgroup.center G)) : Set (G ⧸ Subgroup.center G)) := by
      rw [hN, Subgroup.map_comap_eq_self_of_surjective hsurj]
    rw [h3] at h2
    exact h2

theorem map_center_ne_bot {Q : Subgroup G} (hQc : ¬ Q ≤ Subgroup.center G) :
    Q.map (QuotientGroup.mk' (Subgroup.center G)) ≠ ⊥ := by
  intro hb
  apply hQc
  intro y hy
  have : QuotientGroup.mk' (Subgroup.center G) y ∈ Q.map (QuotientGroup.mk' (Subgroup.center G)) :=
    ⟨y, hy, rfl⟩
  rw [hb, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff y).1 this

theorem lieQConstrained_central_cover (hL : LieQConstrained q) (hsimple : IsSimpleGroup (G ⧸ Subgroup.center G))
    (hnab : ∃ a b : G ⧸ Subgroup.center G, a * b ≠ b * a)
    (hChev : IsChevOfChar q (G ⧸ Subgroup.center G))
    (hZ : Nat.Coprime (Nat.card (Subgroup.center G)) q) {Q : Subgroup G} (hQp : IsPGroup q ↥Q)
    (hQc : ¬ Q ≤ Subgroup.center G) :
    ∀ x ∈ Subgroup.normalizer (Q : Set G),
      (∀ t ∈ pCoreOf q (Subgroup.normalizer (Q : Set G)), x * t = t * x) →
      ∃ t ∈ pCoreOf q (Subgroup.normalizer (Q : Set G)), ∃ z ∈ Subgroup.center G, x = t * z := by
  intro x hx hcomm
  have hQb := map_center_ne_bot hQc
  have hQbp : IsPGroup q ↥(Q.map (QuotientGroup.mk' (Subgroup.center G))) :=
    hQp.map (QuotientGroup.mk' (Subgroup.center G))
  have hO := pCoreOf_normalizer_map_eq hZ hQp
  have hxn : QuotientGroup.mk' (Subgroup.center G) x ∈ Subgroup.normalizer
      ((Q.map (QuotientGroup.mk' (Subgroup.center G)) : Subgroup (G ⧸ Subgroup.center G)) :
        Set (G ⧸ Subgroup.center G)) :=
    Subgroup.le_normalizer_map (QuotientGroup.mk' (Subgroup.center G)) ⟨x, hx, rfl⟩
  have hres := lieQConstrained_inner hL hsimple hnab hChev hQb hQbp _ hxn (fun r hr => by
    rw [hO] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    rw [← map_mul, ← map_mul, hcomm t ht])
  rw [hO] at hres
  obtain ⟨t, ht, hte⟩ := hres
  refine ⟨t, ht, t⁻¹ * x, ?_, by group⟩
  exact QuotientGroup.eq.1 hte

theorem lieQConstrained_aut_central_cover (hL : LieQConstrained q) (hsimple : IsSimpleGroup (G ⧸ Subgroup.center G))
    (hnab : ∃ a b : G ⧸ Subgroup.center G, a * b ≠ b * a)
    (hChev : IsChevOfChar q (G ⧸ Subgroup.center G))
    (hZ : Nat.Coprime (Nat.card (Subgroup.center G)) q) (hperf : commutator G = ⊤)
    {Q : Subgroup G} (hQp : IsPGroup q ↥Q) (hQc : ¬ Q ≤ Subgroup.center G)
    (α : MulAut G) {m : ℕ} (hm : Nat.Coprime m q) (hα : α ^ m = 1)
    (hQfix : ∀ x ∈ Q, α x = x)
    (hTfix : ∀ t ∈ pCoreOf q (Subgroup.normalizer (Q : Set G)), α t = t) : α = 1 := by
  have hQb := map_center_ne_bot hQc
  have hQbp : IsPGroup q ↥(Q.map (QuotientGroup.mk' (Subgroup.center G))) :=
    hQp.map (QuotientGroup.mk' (Subgroup.center G))
  have hO := pCoreOf_normalizer_map_eq hZ hQp
  refine autCenterQuot_injective_of_perfect hperf ?_
  rw [map_one]
  refine lieQConstrained_aut hL hsimple hnab hChev (autCenterQuot G α) hm (by rw [← map_pow, hα, map_one])
    hQb hQbp ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    show autCenterQuot G α ((x : G) : G ⧸ Subgroup.center G) = (x : G ⧸ Subgroup.center G)
    rw [autCenterQuot_mk, hQfix x hx]
  · intro s hs
    rw [hO] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    show autCenterQuot G α ((t : G) : G ⧸ Subgroup.center G) = (t : G ⧸ Subgroup.center G)
    rw [autCenterQuot_mk, hTfix t ht]

end KLevel

section PerfectTools

theorem isQuasisimple_native' {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨hQ.1⟩, hQ.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩

theorem commute_of_forall_commutator_mem_center {Y : Type*} [Group Y] {J : Subgroup Y}
    (hperf : commutator ↥J = ⊤) {y : Y}
    (h : ∀ j : ↥J, ∃ c ∈ Subgroup.center ↥J, (c : Y) = (j : Y) * y * (j : Y)⁻¹ * y⁻¹) :
    ∀ j ∈ J, j * y = y * j := by
  choose c hc hcj using h
  let δ : ↥J →* ↥(Subgroup.center ↥J) := MonoidHom.mk' (fun j => ⟨c j, hc j⟩) (by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    show ((c (a * b) : ↥J) : Y) = ((c a : ↥J) : Y) * ((c b : ↥J) : Y)
    have hcb : ((c b : ↥J) : Y) = (b : Y) * y * (b : Y)⁻¹ * y⁻¹ := hcj b
    have hca : ((c a : ↥J) : Y) = (a : Y) * y * (a : Y)⁻¹ * y⁻¹ := hcj a
    have hab : ((c (a * b) : ↥J) : Y) = ((a * b : ↥J) : Y) * y * ((a * b : ↥J) : Y)⁻¹ * y⁻¹ :=
      hcj (a * b)
    have hcen : (a : Y) * ((c b : ↥J) : Y) = ((c b : ↥J) : Y) * (a : Y) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 (hc b) a)
    have hcomm : ((c a : ↥J) : Y) * ((c b : ↥J) : Y) = ((c b : ↥J) : Y) * ((c a : ↥J) : Y) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 (hc b) (c a))
    have hby : ((c b : ↥J) : Y) * y = (b : Y) * y * (b : Y)⁻¹ := by rw [hcb]; group
    calc ((c (a * b) : ↥J) : Y)
        = (a : Y) * ((b : Y) * y * (b : Y)⁻¹) * (a : Y)⁻¹ * y⁻¹ := by
          rw [hab]; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
      _ = (a : Y) * (((c b : ↥J) : Y) * y) * (a : Y)⁻¹ * y⁻¹ := by rw [hby]
      _ = ((a : Y) * ((c b : ↥J) : Y) * (a : Y)⁻¹) * ((a : Y) * y * (a : Y)⁻¹ * y⁻¹) := by group
      _ = ((c b : ↥J) : Y) * ((c a : ↥J) : Y) := by rw [hcen, hca]; group
      _ = ((c a : ↥J) : Y) * ((c b : ↥J) : Y) := hcomm.symm)
  have hker : commutator ↥J ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [hperf] at hker
  intro j hj
  have h1 : δ ⟨j, hj⟩ = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top _))
  have h2 : ((c ⟨j, hj⟩ : ↥J) : Y) = 1 :=
    congrArg (fun z : ↥(Subgroup.center ↥J) => ((z : ↥J) : Y)) h1
  have h3 : (j : Y) * y * (j : Y)⁻¹ * y⁻¹ = 1 := by rw [← hcj ⟨j, hj⟩]; exact h2
  calc j * y = (j * y * j⁻¹ * y⁻¹) * (y * j) := by group
    _ = y * j := by rw [h3, one_mul]

theorem mem_center_of_mem_pGroup {Y : Type*} [Group Y] [Finite Y] {J T : Subgroup Y}
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hJ3 : 3 ∣ Nat.card ↥J) (hT : IsPGroup 2 ↥T)
    (hJT : ∀ j ∈ J, ∀ t ∈ T, j * t * j⁻¹ ∈ T) :
    ∀ u ∈ J, u ∈ T → ∃ c ∈ Subgroup.center ↥J, (c : Y) = u := by
  set U : Subgroup ↥J := (J ⊓ T).subgroupOf J with hU
  have hUn : U.Normal := ⟨fun n hn g => by
    rw [hU, Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨(g * n * g⁻¹).2, hJT g g.2 n hn.2⟩⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (isQuasisimple_native' hJq) hUn
    with htop | hcen
  · exfalso
    have hJT' : J ≤ T := by
      intro u hu
      have : (⟨u, hu⟩ : ↥J) ∈ U := htop ▸ Subgroup.mem_top _
      rw [hU, Subgroup.mem_subgroupOf] at this
      exact this.2
    obtain ⟨n, hn⟩ := hT.exists_card_eq
    have h1 : 3 ∣ 2 ^ n := hn ▸ hJ3.trans (Subgroup.card_dvd_of_le hJT')
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  · intro u hu huT
    exact ⟨⟨u, hu⟩, hcen (by rw [hU, Subgroup.mem_subgroupOf]; exact ⟨hu, huT⟩), rfl⟩

end PerfectTools

section Generation

theorem not_isCyclic_of_elemAbelian_nine {Y : Type*} [Group Y] {E : Subgroup Y}
    (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) : ¬ IsCyclic ↥E := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E)
  have h3 : g ^ 3 = 1 := Subtype.ext (hE.2 g g.2)
  have hdvd : Nat.card E ∣ 3 := hg ▸ orderOf_dvd_of_pow_eq_one h3
  rw [hE9] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem le_of_inf_centralizer_le_three {Y : Type*} [Group Y] [Finite Y] {E T P : Subgroup Y}
    (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hT : IsPGroup 2 ↥T)
    (hET : E ≤ Subgroup.normalizer (T : Set Y))
    (hle : ∀ b ∈ E, b ≠ 1 → ∀ t ∈ T, b * t = t * b → t ∈ P) : T ≤ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsMulCommutative ↥E := hE.1
  letI : CommGroup ↥E := IsMulCommutative.instCommGroup
  haveI : Fact (IsPGroup 3 ↥E) :=
    ⟨fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩⟩
  letI : MulDistribMulAction ↥E ↥T := MulDistribMulAction.compHom T (Subgroup.inclusion hET)
  have hcop : Nat.Coprime 3 (Nat.card ↥T) := by
    obtain ⟨n, hn⟩ := hT.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hgen := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := ↥T) (A := ↥E) 3 hcop (not_isCyclic_of_elemAbelian_nine hE hE9)
  have hle' : (⨆ (a : ↥E) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) ↥T) ≤
      P.comap T.subtype := by
    refine iSup_le fun a => iSup_le fun ha => ?_
    intro r hr
    change ∀ c : Subgroup.zpowers a, c • r = r at hr
    have hafix := hr ⟨a, Subgroup.mem_zpowers a⟩
    have hc : a.val * r.val * a.val⁻¹ = r.val := congrArg Subtype.val hafix
    have hcomm : a.val * r.val = r.val * a.val := by
      calc a.val * r.val = (a.val * r.val * a.val⁻¹) * a.val := by group
        _ = r.val * a.val := by rw [hc]
    exact hle a.val a.property (fun h => ha (Subtype.ext h)) r.val r.property hcomm
  intro y hy
  have hmem : (⟨y, hy⟩ : ↥T) ∈
      (⨆ (a : ↥E) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) ↥T) := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact hle' hmem

end Generation

theorem coprime_card_center_two {K : Type*} [Group K] [Finite K] (h : GLAPPrimeCore 3 K = ⊥) :
    Nat.Coprime (Nat.card (Subgroup.center K)) 2 := by
  by_contra hcop
  have h2 : 2 ∣ Nat.card (Subgroup.center K) := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at hcop
    exact not_not.1 hcop
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center K)) 2 h2
  have hz'o : orderOf (z : K) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hzc : (z : K) ∈ Subgroup.center K := z.2
  have hN : (Subgroup.zpowers (z : K)).Normal := ⟨fun n hn g => by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g (z : K) := (Subgroup.mem_center_iff.1 hzc g)
    have : g * (z : K) ^ j * g⁻¹ = (z : K) ^ j := by
      rw [(Commute.zpow_right hc j).eq]; group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j⟩
  have hle : Subgroup.zpowers (z : K) ≤ GLAPPrimeCore 3 K :=
    le_sSup (show Subgroup.zpowers (z : K) ∈
      {N : Subgroup K | N.Normal ∧ Nat.Coprime 3 (Nat.card N)} from
      ⟨hN, by rw [Nat.card_zpowers, hz'o]; norm_num⟩)
  rw [h] at hle
  have h1 : (z : K) ∈ (⊥ : Subgroup K) := hle (Subgroup.mem_zpowers _)
  rw [Subgroup.mem_bot] at h1
  rw [h1, orderOf_one] at hz'o
  omega

section YLevel

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def radK (q : ℕ) (K Q : Subgroup Y) : Subgroup Y :=
  (pCoreOf q (Subgroup.normalizer ((Q.subgroupOf K : Subgroup ↥K) : Set ↥K))).map K.subtype

theorem radK_le (q : ℕ) (K Q : Subgroup Y) : radK q K Q ≤ K := Subgroup.map_subtype_le _

theorem radK_isPGroup (q : ℕ) [Fact q.Prime] (K Q : Subgroup Y) : IsPGroup q ↥(radK q K Q) :=
  (pCoreOf_isPGroup q _).map K.subtype

theorem conj_mem_radK (q : ℕ) [Fact q.Prime] {K Q : Subgroup Y} (hQK : Q ≤ K) {e : Y}
    (heK : e ∈ Subgroup.normalizer (K : Set Y)) (heQ : e ∈ Subgroup.normalizer (Q : Set Y))
    {t : Y} (ht : t ∈ radK q K Q) : e * t * e⁻¹ ∈ radK q K Q := by
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨e, heK⟩ with hα
  have hconj : ∀ k : ↥K, ((α k : ↥K) : Y) = e * k * e⁻¹ := fun k => rfl
  have hQα : (Q.subgroupOf K).map α.toMonoidHom = Q.subgroupOf K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : Y) ∈ Q := hy
      have := (Subgroup.mem_normalizer_iff.1 heQ (y : Y)).1 hy'
      show ((α y : ↥K) : Y) ∈ Q
      rw [hconj]; exact this
    · intro hx
      have hx' : (x : Y) ∈ Q := hx
      have heinv : e⁻¹ ∈ Subgroup.normalizer (Q : Set Y) := Subgroup.inv_mem _ heQ
      have heinvK : e⁻¹ ∈ Subgroup.normalizer (K : Set Y) := Subgroup.inv_mem _ heK
      have h1 : e⁻¹ * (x : Y) * e⁻¹⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 heinv (x : Y)).1 hx'
      have h1K : e⁻¹ * (x : Y) * e⁻¹⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.1 heinvK (x : Y)).1 x.2
      refine ⟨⟨e⁻¹ * (x : Y) * e⁻¹⁻¹, h1K⟩, h1, ?_⟩
      apply Subtype.ext
      show e * (e⁻¹ * (x : Y) * e⁻¹⁻¹) * e⁻¹ = x
      group
  have hN : (Subgroup.normalizer ((Q.subgroupOf K : Subgroup ↥K) : Set ↥K)).map α.toMonoidHom =
      Subgroup.normalizer ((Q.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.map_equiv_normalizer_eq, hQα]
  have hinv : (pCoreOf q (Subgroup.normalizer ((Q.subgroupOf K : Subgroup ↥K) : Set ↥K))).map
      α.toMonoidHom = pCoreOf q (Subgroup.normalizer ((Q.subgroupOf K : Subgroup ↥K) : Set ↥K)) := by
    rw [← pCoreOf_map_mulEquiv q α, hN]
  obtain ⟨t', ht', rfl⟩ := ht
  have : α t' ∈ pCoreOf q (Subgroup.normalizer ((Q.subgroupOf K : Subgroup ↥K) : Set ↥K)) := by
    rw [← hinv]; exact ⟨t', ht', rfl⟩
  exact ⟨α t', this, hconj t'⟩

theorem radK_constrained {q : ℕ} [Fact q.Prime] (hL : LieQConstrained q) {K Q : Subgroup Y}
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hChev : IsChevOfChar q (↥K ⧸ Subgroup.center ↥K))
    (hZ : Nat.Coprime (Nat.card (Subgroup.center ↥K)) q) (hQK : Q ≤ K) (hQp : IsPGroup q ↥Q)
    (hQc : ¬ Q ≤ centerIn K) {x : Y} (hxK : x ∈ K) (hxQ : x ∈ Subgroup.normalizer (Q : Set Y))
    (hcomm : ∀ t ∈ radK q K Q, x * t = t * x) :
    ∃ t ∈ radK q K Q, ∃ z ∈ centerIn K, x = t * z := by
  have hQ'p : IsPGroup q ↥(Q.subgroupOf K) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  have hQ'c : ¬ Q.subgroupOf K ≤ Subgroup.center ↥K := by
    intro h
    apply hQc
    intro y hy
    exact ⟨⟨y, hQK hy⟩, h (show (⟨y, hQK hy⟩ : ↥K) ∈ Q.subgroupOf K from hy), rfl⟩
  have hx' : (⟨x, hxK⟩ : ↥K) ∈
      Subgroup.normalizer ((Q.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.mem_normalizer_iff] at hxQ ⊢
    intro y
    exact hxQ (y : Y)
  obtain ⟨t, ht, z, hz, hxt⟩ := lieQConstrained_central_cover hL hKq.2
    (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥K hKq) hChev hZ hQ'p
    hQ'c ⟨x, hxK⟩ hx' (fun t ht => Subtype.ext (hcomm (t : Y) ⟨t, ht, rfl⟩))
  exact ⟨(t : Y), ⟨t, ht, rfl⟩, (z : Y), ⟨z, hz, rfl⟩, congrArg Subtype.val hxt⟩

theorem radK_aut_trivial {q : ℕ} [Fact q.Prime] (hL : LieQConstrained q) {K Q : Subgroup Y}
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hChev : IsChevOfChar q (↥K ⧸ Subgroup.center ↥K))
    (hZ : Nat.Coprime (Nat.card (Subgroup.center ↥K)) q) (hQK : Q ≤ K) (hQp : IsPGroup q ↥Q)
    (hQc : ¬ Q ≤ centerIn K) {b : Y} (hbK : b ∈ Subgroup.normalizer (K : Set Y)) {m : ℕ}
    (hm : Nat.Coprime m q) (hbm : b ^ m = 1) (hbQ : ∀ x ∈ Q, b * x = x * b)
    (hbT : ∀ t ∈ radK q K Q, b * t = t * b) : ∀ k ∈ K, b * k = k * b := by
  have hQ'p : IsPGroup q ↥(Q.subgroupOf K) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
  have hQ'c : ¬ Q.subgroupOf K ≤ Subgroup.center ↥K := by
    intro h
    apply hQc
    intro y hy
    exact ⟨⟨y, hQK hy⟩, h (show (⟨y, hQK hy⟩ : ↥K) ∈ Q.subgroupOf K from hy), rfl⟩
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨b, hbK⟩ with hα
  have hconj : ∀ k : ↥K, ((α k : ↥K) : Y) = b * k * b⁻¹ := fun k => rfl
  have hαm : α ^ m = 1 := by
    have h0 : α ^ m = K.normalizerMonoidHom ((⟨b, hbK⟩ : ↥(Subgroup.normalizer (K : Set Y))) ^ m) :=
      by rw [map_pow]
    rw [h0]
    have h1 : (⟨b, hbK⟩ : ↥(Subgroup.normalizer (K : Set Y))) ^ m = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hbm)
    rw [h1, map_one]
  have hcomm_fix : ∀ k : ↥K, b * (k : Y) = (k : Y) * b → α k = k := by
    intro k hk
    apply Subtype.ext
    rw [hconj]
    calc b * (k : Y) * b⁻¹ = (k : Y) * b * b⁻¹ := by rw [hk]
      _ = k := by group
  have hα1 := lieQConstrained_aut_central_cover hL hKq.2
    (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥K hKq) hChev hZ hKq.1
    hQ'p hQ'c α hm hαm (fun x hx => hcomm_fix x (hbQ (x : Y) hx))
    (fun t ht => hcomm_fix t (hbT (t : Y) ⟨t, ht, rfl⟩))
  intro k hk
  have h1 := congrArg (fun γ : MulAut ↥K => ((γ ⟨k, hk⟩ : ↥K) : Y)) hα1
  simp only [MulAut.one_apply] at h1
  rw [hconj] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

end YLevel

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
