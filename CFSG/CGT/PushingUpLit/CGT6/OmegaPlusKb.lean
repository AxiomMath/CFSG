module

public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusDefs
public import CFSG.CGT.PushingUpLit.CGT6.EmbTight
public import CFSG.CGT.PushingUpLit.CGT6.EmbSix

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.ComponentClassification CFSG.RankThree.PartOne CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {V : Type} [CommGroup V]

@[expose] def kStab (G : Subgroup (MulAut V)) (b : MulAut V) : Subgroup (MulAut V) :=
  G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)) ⊓ fixW (fixV (Subgroup.zpowers b))

theorem sq_apply_eq {b : MulAut V} (hb : b ^ 2 = 1) (v : V) : b (b v) = v := by
  have : (b ^ 2) v = v := by rw [hb]; rfl
  simpa [pow_two, MulAut.mul_apply] using this

theorem mem_kStab {G : Subgroup (MulAut V)} {b k : MulAut V} :
    k ∈ kStab G b ↔ (k ∈ G ∧ k * b = b * k) ∧ ∀ v ∈ fixV (Subgroup.zpowers b), k v = v := by
  unfold kStab
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
    mem_fixW]
  constructor
  · rintro ⟨⟨hG, hc⟩, hf⟩
    exact ⟨⟨hG, hc.symm⟩, hf⟩
  · rintro ⟨⟨hG, hc⟩, hf⟩
    exact ⟨⟨hG, hc.symm⟩, hf⟩

theorem inv_eq_self_of_exp (hV : ∀ v : V, v ^ 2 = 1) (x : V) : x⁻¹ = x := by
  have := hV x
  rw [pow_two] at this
  exact inv_eq_of_mul_eq_one_right this

theorem kStab_mul_inv_mem (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)} {b k : MulAut V}
    (hb : b ^ 2 = 1) (hk : k ∈ kStab G b) (v : V) :
    k v * v⁻¹ ∈ fixV (Subgroup.zpowers b) := by
  rw [mem_fixV_zpowers_iff]
  obtain ⟨⟨-, hkb⟩, hkf⟩ := mem_kStab.mp hk
  have hw : b (b v * v⁻¹) = b v * v⁻¹ := by
    rw [map_mul, map_inv, sq_apply_eq hb, ← inv_eq_self_of_exp hV (b v * v⁻¹), mul_inv_rev, inv_inv,
      mul_comm]
  have hkw := hkf _ ((mem_fixV_zpowers_iff).mpr hw)
  have hbk : b (k v) = k (b v) := by
    have := congrArg (fun x : MulAut V => x v) hkb
    simpa [MulAut.mul_apply] using this.symm
  rw [map_mul, map_inv, hbk]
  rw [map_mul, map_inv] at hkw
  have h2 : k (b v) = b v * v⁻¹ * k v := by
    rw [mul_inv_eq_iff_eq_mul] at hkw
    exact hkw
  rw [h2, mul_comm (b v) v⁻¹, mul_comm (v⁻¹ * b v) (k v), mul_assoc, mul_assoc, mul_inv_cancel,
    mul_one]

theorem kStab_abelian (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)} {b : MulAut V}
    (hb : b ^ 2 = 1) :
    (∀ k₁ ∈ kStab G b, ∀ k₂ ∈ kStab G b, k₁ * k₂ = k₂ * k₁) ∧ ∀ k ∈ kStab G b, k ^ 2 = 1 := by
  have key : ∀ k ∈ kStab G b, ∀ v : V, k v = (k v * v⁻¹) * v := fun k _ v => by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  constructor
  · intro k₁ h₁ k₂ h₂
    ext v
    have a1 := (mem_kStab.mp h₁).2 _ (kStab_mul_inv_mem hV hb h₂ v)
    have a2 := (mem_kStab.mp h₂).2 _ (kStab_mul_inv_mem hV hb h₁ v)
    have e1 : k₁ (k₂ v) = (k₂ v * v⁻¹) * k₁ v := by
      conv_lhs => rw [key k₂ h₂ v]
      rw [map_mul, a1]
    have e2 : k₂ (k₁ v) = (k₁ v * v⁻¹) * k₂ v := by
      conv_lhs => rw [key k₁ h₁ v]
      rw [map_mul, a2]
    show k₁ (k₂ v) = k₂ (k₁ v)
    rw [e1, e2]
    ac_rfl
  · intro k hk
    ext v
    have a := (mem_kStab.mp hk).2 _ (kStab_mul_inv_mem hV hb hk v)
    have e : k (k v) = (k v * v⁻¹) * k v := by
      conv_lhs => rw [key k hk v]
      rw [map_mul, a]
    show k (k v) = v
    rw [e]
    calc k v * v⁻¹ * k v = (k v * k v) * v⁻¹ := by ac_rfl
      _ = v := by rw [← pow_two, hV, one_mul, inv_eq_self_of_exp hV]

theorem kStab_conj_mem {G : Subgroup (MulAut V)} {b g k : MulAut V} (hg : g ∈ G)
    (hgb : g * b = b * g) (hk : k ∈ kStab G b) : g * k * g⁻¹ ∈ kStab G b := by
  obtain ⟨⟨hkG, hkb⟩, hkf⟩ := mem_kStab.mp hk
  refine mem_kStab.mpr ⟨⟨G.mul_mem (G.mul_mem hg hkG) (G.inv_mem hg), ?_⟩, ?_⟩
  · have hc : Commute g b := hgb
    have hc' : Commute k b := hkb
    exact (((hc.mul_left hc').mul_left hc.inv_left) : Commute (g * k * g⁻¹) b)
  · intro v hv
    have hgv : g⁻¹ v ∈ fixV (Subgroup.zpowers b) := by
      rw [mem_fixV_zpowers_iff] at hv ⊢
      have h1 : g⁻¹ * b = b * g⁻¹ := by
        have : Commute g⁻¹ b := (Commute.inv_left (show Commute g b from hgb))
        exact this
      have := congrArg (fun x : MulAut V => x v) h1
      simp only [MulAut.mul_apply] at this
      rw [← this, hv]
    have := hkf _ hgv
    simp only [MulAut.mul_apply]
    rw [this]
    exact congrArg (fun x : MulAut V => x v) (mul_inv_cancel g)

theorem kStab_centralizes [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G D : Subgroup (MulAut V)}
    {b t : MulAut V} (hb2 : b ^ 2 = 1) (ht2 : t ^ 2 = 1) (htG : t ∈ G) (hbt : b * t = t * b)
    (hDG : D ≤ G) (hDb : D ≤ Subgroup.centralizer ({b} : Set (MulAut V)))
    (hDt : D ≤ Subgroup.centralizer ({t} : Set (MulAut V)))
    (hDsub : (D.subgroupOf (G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)))).IsSubnormal)
    (hNo : SubTwo.NoTwoQuotient D) (hperf : ⁅D, D⁆ = D) (hO : ⁅oTwoIn D, D⁆ = ⊥)
    (hVD : commV D ⊔ fixV (Subgroup.zpowers b) = ⊤) (hWb : fixV D ≤ fixV (Subgroup.zpowers b))
    (hVt : ∀ v : V, t v * v⁻¹ ∈ fixV D) :
    ∀ k ∈ kStab G b, ∀ d ∈ D, k * d = d * k := by
  classical
  have hab := kStab_abelian hV (G := G) hb2
  have ht1 : t⁻¹ = t := by
    have : t * t = 1 := by rw [← pow_two]; exact ht2
    exact inv_eq_of_mul_eq_one_right this
  set Q : Subgroup (MulAut V) := kStab G b ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) with hQ
  have hQ2 : IsPGroup 2 ↥Q := fun q => ⟨1, Subtype.ext (by simpa using hab.2 q.1 q.2.1)⟩
  set H : Subgroup (MulAut V) := G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)) ⊓
    Subgroup.centralizer ({t} : Set (MulAut V)) with hH
  have hHle : H ≤ G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) := fun x hx => ⟨hx.1.1, hx.2⟩
  have hs : (D.subgroupOf H).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hHle hDsub
  have hDH : D ≤ H := fun x hx => ⟨⟨hDG hx, hDb hx⟩, hDt hx⟩
  have hQH : Q ≤ H := fun x hx => by
    obtain ⟨⟨hxG, hxb⟩, -⟩ := mem_kStab.mp hx.1
    exact ⟨⟨hxG, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh; subst hh; exact hxb.symm⟩, hx.2⟩
  have hconj : ∀ d ∈ D, ∀ x ∈ Q, d * x * d⁻¹ ∈ Q := by
    intro d hd x hx
    have hdb : d * b = b * d := Subgroup.mem_centralizer_singleton_iff.mp (hDb hd)
    have hdt : Commute d t := Subgroup.mem_centralizer_singleton_iff.mp (hDt hd)
    have hxt : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    exact ⟨kStab_conj_mem (hDG hd) hdb hx.1,
      Subgroup.mem_centralizer_singleton_iff.mpr ((hdt.mul_left hxt).mul_left hdt.inv_left)⟩
  have hDQ : D ≤ Subgroup.normalizer (Q : Set (MulAut V)) := fun d hd =>
    Subgroup.mem_normalizer_iff.mpr fun h => ⟨hconj d hd h, fun hh => by
      have := hconj d⁻¹ (D.inv_mem hd) _ hh
      simpa [mul_assoc] using this⟩
  have hQD : ⁅Q, D⁆ = ⊥ :=
    commutator_eq_bot_of_subnormal_sup hNo hQ2 hDQ hDH hQH hs hO (Or.inl hperf)
  have htb : ∀ w ∈ fixV (Subgroup.zpowers b), t w ∈ fixV (Subgroup.zpowers b) := by
    intro w hw
    rw [mem_fixV_zpowers_iff] at hw ⊢
    have := congrArg (fun x : MulAut V => x w) hbt
    simp only [MulAut.mul_apply] at this
    rw [this, hw]
  have hker : ∀ k ∈ kStab G b, t * k = k * t := by
    intro k hk
    set k' : MulAut V := t * k * t⁻¹ with hk'
    have hk'mem : k' ∈ kStab G b := kStab_conj_mem htG hbt.symm hk
    have hcomm : k * k' = k' * k := hab.1 k hk k' hk'mem
    set ψ : MulAut V := k * k' with hψ
    have hψmem : ψ ∈ kStab G b := (kStab G b).mul_mem hk hk'mem
    have e1 : t * k = k' * t := by rw [hk']; group
    have e2 : t * k' = k * t := by
      calc t * k' = (t * t) * k * t⁻¹ := by rw [hk']; group
        _ = k * t := by rw [show t * t = 1 by rw [← pow_two]; exact ht2, one_mul, ht1]
    have hψt : t * ψ = ψ * t := by
      calc t * ψ = (t * k) * k' := by rw [hψ]; group
        _ = k' * (t * k') := by rw [e1]; group
        _ = k' * (k * t) := by rw [e2]
        _ = (k * k') * t := by rw [← mul_assoc, ← hcomm]
    have hψQ : ψ ∈ Q := ⟨hψmem, Subgroup.mem_centralizer_singleton_iff.mpr hψt.symm⟩
    have hψD : ∀ d ∈ D, ψ * d = d * ψ := by
      intro d hd
      have h1 : ⁅ψ, d⁆ ∈ ⁅Q, D⁆ := Subgroup.commutator_mem_commutator hψQ hd
      rw [hQD] at h1
      have h1' : ⁅ψ, d⁆ = 1 := h1
      rw [commutatorElement_def] at h1'
      calc ψ * d = (ψ * d * ψ⁻¹ * d⁻¹) * (d * ψ) := by group
        _ = d * ψ := by rw [h1', one_mul]
    have hη : ∀ v : V, ψ v * v⁻¹ ∈ fixV D := by
      intro v
      have hinvV := inv_eq_self_of_exp hV
      have hkf : ∀ w ∈ fixV (Subgroup.zpowers b), k w = w := (mem_kStab.mp hk).2
      have hφ : ∀ w, k w * w⁻¹ ∈ fixV (Subgroup.zpowers b) := fun w =>
        kStab_mul_inv_mem hV hb2 hk w
      have htt : ∀ w, t (t w) = w := sq_apply_eq ht2
      obtain ⟨c, hc⟩ : ∃ c : V, c = t v * v⁻¹ := ⟨_, rfl⟩
      have hcb : c ∈ fixV (Subgroup.zpowers b) := hWb (hc ▸ hVt v)
      have hv' : t v = c * v := by rw [hc, mul_assoc, inv_mul_cancel, mul_one]
      have hkc : k c = c := hkf c hcb
      obtain ⟨φv, hφv⟩ : ∃ φv : V, φv = k v * v⁻¹ := ⟨_, rfl⟩
      have hφvb : φv ∈ fixV (Subgroup.zpowers b) := hφv ▸ hφ v
      have hp : k v = φv * v := by rw [hφv, mul_assoc, inv_mul_cancel, mul_one]
      have htφ : t φv ∈ fixV (Subgroup.zpowers b) := htb _ hφvb
      have htc : t c ∈ fixV (Subgroup.zpowers b) := htb _ hcb
      have hψv : ψ v = k (t (k (t v))) := by
        show k (k' v) = _
        simp only [hk', MulAut.mul_apply, ht1]
      have e1 : k (t v) = c * k v := by rw [hv', map_mul, hkc]
      have e3 : t (k v) = t φv * t v := by rw [hp, map_mul]
      have e5 : k (t (k v)) = t φv * (c * k v) := by
        rw [e3, map_mul, hkf _ htφ, e1]
      have e4 : k (t (k (t v))) = t c * (t φv * (c * k v)) := by
        rw [e1, map_mul t, map_mul k, hkf _ htc, e5]
      have step : ψ v = t c * (t φv * (c * k v)) := by rw [hψv, e4]
      have htcc : t c * c = 1 := by
        have h1 : t c = v * (t v)⁻¹ := by rw [hc, map_mul, map_inv, htt]
        rw [h1, hc]
        group
      have hfin : ψ v * v⁻¹ = t φv * φv⁻¹ := by
        calc ψ v * v⁻¹ = t φv * ((t c * c) * (k v * v⁻¹)) := by rw [step]; ac_rfl
          _ = t φv * φv⁻¹ := by rw [htcc, one_mul, ← hφv, hinvV φv]
      rw [hfin]
      exact hVt φv
    have hψ1 : ψ = 1 := by
      have hN : (⊤ : Subgroup V) ≤ fixV (Subgroup.zpowers ψ) := by
        rw [← hVD]
        refine sup_le ?_ ?_
        · rw [commV, Subgroup.closure_le]
          rintro _ ⟨d, hd, v, rfl⟩
          rw [SetLike.mem_coe, mem_fixV_zpowers_iff]
          have hηd : d (ψ v * v⁻¹) = ψ v * v⁻¹ := hη v d hd
          have hψd : ψ (d v) = d (ψ v) := by
            have := congrArg (fun x : MulAut V => x v) (hψD d hd)
            simpa [MulAut.mul_apply] using this
          rw [map_mul, map_inv, hψd]
          rw [map_mul, map_inv] at hηd
          have h2 : d (ψ v) = ψ v * v⁻¹ * d v := by
            rw [mul_inv_eq_iff_eq_mul] at hηd
            exact hηd
          rw [h2]
          calc ψ v * v⁻¹ * d v * (ψ v)⁻¹ = (ψ v * (ψ v)⁻¹) * (d v * v⁻¹) := by ac_rfl
            _ = d v * v⁻¹ := by rw [mul_inv_cancel, one_mul]
        · intro w hw
          rw [mem_fixV_zpowers_iff]
          exact (mem_kStab.mp hψmem).2 w hw
      ext v
      exact (mem_fixV_zpowers_iff.mp (hN (Subgroup.mem_top v)))
    have hkk : k' = k := by
      have h1 : k * k' = 1 := hψ1
      have h2 : k' = k⁻¹ := (eq_inv_of_mul_eq_one_right h1)
      rw [h2]
      exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hab.2 k hk)
    rw [e1, hkk]
  intro k hk d hd
  have hkQ : k ∈ Q := ⟨hk, Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh; subst hh; exact hker k hk⟩
  have : ⁅k, d⁆ = 1 := by
    have h1 : ⁅k, d⁆ ∈ ⁅Q, D⁆ := Subgroup.commutator_mem_commutator hkQ hd
    rw [hQD] at h1
    exact h1
  rw [commutatorElement_def] at this
  calc k * d = (k * d * k⁻¹ * d⁻¹) * (d * k) := by group
    _ = d * k := by rw [this, one_mul]

theorem commutator_self_of_commutator_eq_top {Γ : Type*} [Group Γ] {D : Subgroup Γ}
    (h : commutator ↥D = ⊤) : ⁅D, D⁆ = D := by
  have h1 : (⊤ : Subgroup ↥D).map D.subtype = D := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  calc ⁅D, D⁆ = ⁅(⊤ : Subgroup ↥D).map D.subtype, (⊤ : Subgroup ↥D).map D.subtype⁆ := by
        rw [h1]
    _ = (⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆).map D.subtype :=
        (Subgroup.map_commutator _ _ _).symm
    _ = (⊤ : Subgroup ↥D).map D.subtype := by rw [← commutator_def, h]
    _ = D := h1

theorem PlusSide.dfacts [Finite V] {G Y D B : Subgroup (MulAut V)} {n : ℕ}
    (hP : PlusSide G Y D B n) :
    ⁅D, D⁆ = D ∧ SubTwo.NoTwoQuotient D ∧ ⁅oTwoIn D, D⁆ = ⊥ := by
  obtain ⟨θ⟩ := hP.dsl
  have hqs : CFSG.Open.IsQuasisimple ↥D :=
    Components.quasisimple_of_equiv θ (isQuasisimple_sl2_gf hP.hn)
  have hperf : ⁅D, D⁆ = D := commutator_self_of_commutator_eq_top hqs.1
  refine ⟨hperf, noTwoQuotient_of_perfect hperf, ?_⟩
  have hp : pCore 2 ↥D = ⊥ := pCore_eq_bot_of_equiv θ (pCore_sl2_eq_bot hP.hn)
  have ho : oTwoIn D = ⊥ := by
    show (pCore 2 ↥D).map D.subtype = ⊥
    rw [hp, Subgroup.map_bot]
  rw [ho]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr bot_le

theorem PlusSide.dnormal {G Y D B : Subgroup (MulAut V)} {n : ℕ} (hP : PlusSide G Y D B n) :
    (D.subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hP.dy, ← hP.sup]
  refine sup_le Subgroup.le_normalizer fun x hx => Subgroup.mem_normalizer_iff.mpr fun h => ?_
  have hc : ∀ y ∈ B, ∀ d ∈ D, y * d * y⁻¹ = d := fun y hy d hd => by
    rw [← hP.comm d hd y hy, mul_assoc, mul_inv_cancel, mul_one]
  constructor
  · intro hh
    rw [hc x hx h hh]
    exact hh
  · intro hh
    have h1 := hc x⁻¹ (B.inv_mem hx) _ hh
    have h2 : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
    rw [h2] at h1
    rw [h1]
    exact hh

theorem kStab_comm_D [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G T Y D B : Subgroup (MulAut V)}
    {n : ℕ} (cfg : Emb4Cfg G T Y) (hP : PlusSide G Y D B n) {b : MulAut V} (hb : b ∈ B)
    (hb2 : b ^ 2 = 1) : ∀ k ∈ kStab G b, ∀ d ∈ D, k * d = d * k := by
  classical
  obtain ⟨t, htT, ht1, ht2', -⟩ := exists_central_involution cfg.adm.hT1 cfg.adm.hT2
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact ht2'
  have hYG : Y ≤ G := hP.yg
  have htC : t ∈ Subgroup.centralizer (Y : Set (MulAut V)) := cfg.adm.le_centralizer htT
  have htG : t ∈ G := cfg.adm.hTG htT
  have htY : ∀ y ∈ Y, y * t = t * y := fun y hy => Subgroup.mem_centralizer_iff.mp htC y hy
  obtain ⟨hdf, hno, hdo⟩ := hP.dfacts
  have hDY := hP.dy
  have hDG : D ≤ G := hDY.trans hYG
  have hbY : b ∈ Y := hP.by_ hb
  have hbt : b * t = t * b := htY b hbY
  have hDb : D ≤ Subgroup.centralizer ({b} : Set (MulAut V)) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hP.comm d hd b hb)
  have hDt : D ≤ Subgroup.centralizer ({t} : Set (MulAut V)) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.mpr (htY d (hDY hd))
  have hYK : Y ≤ G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) := fun y hy =>
    ⟨hYG hy, Subgroup.mem_centralizer_singleton_iff.mpr (htY y hy)⟩
  have hDsub : (D.subgroupOf (G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)))).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans hDY hYK hP.dnormal.isSubnormal
      (cfg.cent t ⟨htG, htC⟩ ht1 ht2)
  have hfix : fixV Y ≤ fixV (Subgroup.zpowers b) := fun v hv =>
    mem_fixV_zpowers_iff.mpr (hv b hbY)
  have hVD : commV D ⊔ fixV (Subgroup.zpowers b) = ⊤ := by
    apply top_unique
    rw [← hP.vsup, hP.cD, sup_comm]
    exact sup_le_sup_left hfix _
  have hWb : fixV D ≤ fixV (Subgroup.zpowers b) := hP.fD ▸ hfix
  have hVt : ∀ v : V, t v * v⁻¹ ∈ fixV D := by
    intro v
    have hv : v ∈ fixV Y ⊔ commV Y := by rw [hP.vsup]; exact Subgroup.mem_top v
    obtain ⟨w, hw, u, hu, rfl⟩ := Subgroup.mem_sup.mp hv
    have htu : t u = u := hP.ctriv t ⟨htG, htC⟩ ⟨1, by simpa using ht2⟩ u hu
    have htw : t w * w⁻¹ ∈ fixV Y := by
      intro y hy
      have hyt := congrArg (fun x : MulAut V => x w) (htY y hy)
      simp only [MulAut.mul_apply] at hyt
      rw [map_mul, map_inv, hw y hy, hyt, hw y hy]
    rw [hP.fD]
    have : t (w * u) * (w * u)⁻¹ = t w * w⁻¹ := by
      rw [map_mul, htu, mul_inv_rev]
      group
    rw [this]
    exact htw
  exact kStab_centralizes hV hb2 ht2 htG hbt hDG hDb hDt hDsub hno hdf hdo hVD hWb hVt

theorem kStab_le_B [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G T Y D B : Subgroup (MulAut V)} {n : ℕ}
    (cfg : Emb4Cfg G T Y) (hP : PlusSide G Y D B n) {b : MulAut V} (hb : b ∈ B) (hb2 : b ^ 2 = 1)
    (hb1 : b ≠ 1) : kStab G b ≤ B := by
  have hYG : Y ≤ G := hP.yg
  have hbY : b ∈ Y := hP.by_ hb
  have hfix : fixV Y ≤ fixV (Subgroup.zpowers b) := fun v hv =>
    mem_fixV_zpowers_iff.mpr (hv b hbY)
  intro k hk
  have hkD := kStab_comm_D hV cfg hP hb hb2 k hk
  have hkC : k ∈ G ⊓ Subgroup.centralizer (D : Set (MulAut V)) :=
    ⟨(mem_kStab.mp hk).1.1, Subgroup.mem_centralizer_iff.mpr fun d hd => (hkD d hd).symm⟩
  obtain ⟨β, hβB, c, hcC, hkβc⟩ := hP.cdec k hkC
  have hcb : c * b = b * c := (Subgroup.mem_centralizer_iff.mp hcC.2 b hbY).symm
  have hkb : k * b = b * k := (mem_kStab.mp hk).1.2
  have hβ : β = k * c⁻¹ := by rw [hkβc]; group
  have hβb : β * b = b * β := by
    have h1 : Commute k b := hkb
    have h2 : Commute c b := hcb
    rw [hβ]
    exact h1.mul_left h2.inv_left
  have hβK : β ∈ kStab G b :=
    mem_kStab.mpr ⟨⟨hYG (hP.by_ hβB), hβb⟩, hP.rootfix b hb hb2 hb1 β hβB hβb⟩
  have hcK : c ∈ kStab G b := by
    have : c = β⁻¹ * k := by rw [hkβc]; group
    rw [this]
    exact (kStab G b).mul_mem ((kStab G b).inv_mem hβK) hk
  have hc2 : c ^ 2 = 1 := (kStab_abelian hV hb2).2 c hcK
  have hcU : ∀ u ∈ commV Y, c u = u := hP.ctriv c hcC ⟨1, by simpa using hc2⟩
  have hc1 : c = 1 := by
    ext v
    have hv : v ∈ fixV Y ⊔ commV Y := by rw [hP.vsup]; exact Subgroup.mem_top v
    obtain ⟨w, hw, u, hu, rfl⟩ := Subgroup.mem_sup.mp hv
    show c (w * u) = w * u
    rw [map_mul, hcU u hu, (mem_kStab.mp hcK).2 w (hfix hw)]
  rw [hkβc, hc1, mul_one]
  exact hβB

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
