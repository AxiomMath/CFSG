module

public import CFSG.ClassicalInvolution.AschTight.SDStructure
public import CFSG.ClassicalInvolution.AschTight.TzFusion
public import CFSG.ClassicalInvolution.AschTight.E3OddAut

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_mem_zpowers_of_mul_self {t y : G} (ht : t * t = 1)
    (hy : y ∈ Subgroup.zpowers t) : y = 1 ∨ y = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem false_of_card_centralizer_eq_two [Finite G] {V Q : Subgroup G} (hV4 : Nat.card V = 4)
    (hVN : V ≤ Subgroup.normalizer (Q : Set G)) (hQ4 : 4 ∣ Nat.card Q)
    (hfix : ∀ v ∈ V, v ≠ 1 → Nat.card ↥(Q ⊓ Subgroup.centralizer ({v} : Set G)) = 2) : False := by
  classical
  let _ : MulAction ↥V ↥Q :=
    MulAction.compHom ↥Q ((normalizerConj Q).comp (Subgroup.inclusion hVN))
  have : Fintype ↥V := Fintype.ofFinite _
  have : Fintype ↥Q := Fintype.ofFinite _
  have hsmul : ∀ (v : ↥V) (q : ↥Q), ((v • q : ↥Q) : G) = (v : G) * q * (v : G)⁻¹ :=
    fun _ _ => rfl
  have hcard : ∀ v : ↥V, Fintype.card (MulAction.fixedBy ↥Q v) =
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({(v : G)} : Set G)) := by
    intro v
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun q => ⟨((q : ↥Q) : G), (q : ↥Q).2, ?_⟩
        invFun := fun x => ⟨⟨x, x.2.1⟩, ?_⟩
        left_inv := fun q => rfl
        right_inv := fun x => rfl }
    · have h1 : (v : G) * (q : ↥Q) * (v : G)⁻¹ = (q : ↥Q) := by
        rw [← hsmul]
        exact congrArg Subtype.val (MulAction.mem_fixedBy.mp q.2)
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc ((q : ↥Q) : G) * v = (v : G) * (q : ↥Q) * (v : G)⁻¹ * v := by rw [h1]
        _ = v * (q : ↥Q) := by group
    · refine MulAction.mem_fixedBy.mpr (Subtype.ext ?_)
      rw [hsmul]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp x.2.2
      show (v : G) * x * (v : G)⁻¹ = x
      rw [← h1]
      group
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ↥V ↥Q
  have hV4' : Fintype.card ↥V = 4 := by rw [← Nat.card_eq_fintype_card, hV4]
  have h1 : Fintype.card (MulAction.fixedBy ↥Q (1 : ↥V)) = Nat.card Q := by
    rw [hcard]
    congr 2
    refine inf_of_le_left fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr ?_
    simp
  have h2 : ∑ v ∈ Finset.univ.erase (1 : ↥V), Fintype.card (MulAction.fixedBy ↥Q v) = 6 := by
    rw [Finset.sum_congr rfl fun v hv => by
      rw [hcard, hfix v v.2 fun h => (Finset.mem_erase.mp hv).1 (Subtype.ext h)],
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hV4']
    rfl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ↥V)), h1, h2, hV4'] at hB
  omega

theorem mem_of_mem_normalizer_imp [Finite G] {R T : Subgroup G} {t : G} (hT2 : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (R : Set G)) (htT : t ∈ T) (ht2 : t * t = 1)
    {X : Set G} (hX2 : ∀ x ∈ X, x * x = 1) (hXc : ∀ x ∈ X, ∀ y ∈ T, y * x * y⁻¹ ∈ X)
    (htX : t ∈ X)
    (hcl : ∀ s ∈ X, s ∈ T →
      s ∈ Subgroup.normalizer ((R ⊔ Subgroup.zpowers t : Subgroup G) : Set G) →
        s ∈ R ⊔ Subgroup.zpowers t)
    {s : G} (hsX : s ∈ X) (hsT : s ∈ T) : s ∈ R ⊔ Subgroup.zpowers t := by
  classical
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hs2 := hX2 s hsX
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have htP : t ∈ R ⊔ Subgroup.zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : G, t * s = ρ := ⟨_, rfl⟩
  have hρT : ρ ∈ T := hρ ▸ T.mul_mem htT hsT
  have hinv1 : t * ρ * t⁻¹ = ρ⁻¹ := by
    rw [← hρ]
    calc t * (t * s) * t⁻¹ = (t * t) * s * t⁻¹ := by group
      _ = (t * s)⁻¹ := by rw [ht2, one_mul, mul_inv_rev, hsi]
  have hinv : ∀ k : ℕ, t * ρ ^ k * t⁻¹ = (ρ ^ k)⁻¹ := fun k => by
    rw [← conj_pow, hinv1, inv_pow]
  have hnorm : ∀ y ∈ T, y * y = 1 → y * t * y⁻¹ ∈ R ⊔ Subgroup.zpowers t →
      y ∈ Subgroup.normalizer ((R ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := by
    intro y hyT hy2 hyt
    refine mem_normalizer_of_mul_self_eq_one hy2 fun x hx => ?_
    have hle : R ⊔ Subgroup.zpowers t ≤
        (R ⊔ Subgroup.zpowers t).comap (MulAut.conj y).toMonoidHom := by
      refine sup_le (fun r hr => ?_) (Subgroup.zpowers_le.mpr hyt)
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hTN hyT) r).mp hr)
    exact hle hx
  obtain ⟨n, hn⟩ := hT2 ⟨ρ, hρT⟩
  have hex : ∃ j : ℕ, ρ ^ (2 ^ j) ∈ R :=
    ⟨n, by rw [show ρ ^ (2 ^ n) = 1 from congrArg Subtype.val hn]; exact R.one_mem⟩
  obtain ⟨e, he, hmin⟩ : ∃ e : ℕ, ρ ^ (2 ^ e) ∈ R ∧ ∀ j < e, ρ ^ (2 ^ j) ∉ R :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  rcases e with _ | _ | e
  ·
    have hs : s = t * ρ := by rw [← hρ, ← mul_assoc, ht2, one_mul]
    rw [hs]
    exact Subgroup.mul_mem _ htP (Subgroup.mem_sup_left (by simpa using he))
  ·
    refine hcl s hsX hsT (hnorm s hsT hs2 ?_)
    have e1 : s * t * s⁻¹ = t * ρ ^ 2 := by
      rw [← hρ, hsi]
      calc s * t * s = (t * t) * s * t * s := by rw [ht2, one_mul]
        _ = t * (t * s) ^ 2 := by rw [_root_.sq]; group
    rw [e1]
    exact Subgroup.mul_mem _ htP (Subgroup.mem_sup_left (by simpa using he))
  ·
    obtain ⟨d, hd⟩ : ∃ d : G, ρ ^ (2 ^ e) = d := ⟨_, rfl⟩
    obtain ⟨c, hcd⟩ : ∃ c : G, d * d = c := ⟨_, rfl⟩
    have hdT : d ∈ T := hd ▸ T.pow_mem hρT _
    have hc : ρ ^ (2 ^ (e + 1)) = c := by rw [pow_succ, pow_mul, _root_.sq, hd, hcd]
    have hcc : ρ ^ (2 ^ (e + 1 + 1)) = c * c := by
      rw [pow_succ 2 (e + 1), pow_mul, hc, _root_.sq]
    have htd : t * d * t⁻¹ = d⁻¹ := by rw [← hd]; exact hinv _
    have hs' : d⁻¹ * t * d = c⁻¹ * t := by
      calc d⁻¹ * t * d = d⁻¹ * (t * d * t⁻¹) * t := by group
        _ = (d * d)⁻¹ * t := by rw [htd]; group
        _ = c⁻¹ * t := by rw [hcd]
    have hs'X : d⁻¹ * t * d ∈ X := by
      have := hXc t htX d⁻¹ (T.inv_mem hdT)
      rwa [inv_inv] at this
    have hs'T : d⁻¹ * t * d ∈ T := T.mul_mem (T.mul_mem (T.inv_mem hdT) htT) hdT
    have htc : t * c * t⁻¹ = c⁻¹ := by rw [← hc]; exact hinv _
    have hs'N := hnorm _ hs'T (hX2 _ hs'X) (by
      rw [hs']
      have e1 : c⁻¹ * t * t * (c⁻¹ * t)⁻¹ = (c * c)⁻¹ * t := by
        calc c⁻¹ * t * t * (c⁻¹ * t)⁻¹ = c⁻¹ * (t * c * t⁻¹) * t := by group
          _ = (c * c)⁻¹ * t := by rw [htc]; group
      rw [e1, ← hcc]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (R.inv_mem he)) htP)
    have hs'P := hcl _ hs'X hs'T hs'N
    rw [hs'] at hs'P
    have hcP : c ∈ R ⊔ Subgroup.zpowers t := by
      have h1 := Subgroup.mul_mem _ hs'P (Subgroup.inv_mem _ htP)
      rw [mul_inv_cancel_right] at h1
      have h2 := Subgroup.inv_mem _ h1
      rwa [inv_inv] at h2
    have hcR : c ∉ R := by rw [← hc]; exact hmin (e + 1) (by omega)
    obtain ⟨r, hr, hrc⟩ : ∃ r ∈ R, c * t = r :=
      ⟨_, (mem_or_mul_mem_of_mem_sup_zpowers ht2 (hTN htT) hcP).resolve_left hcR, rfl⟩
    have hcomm : c * ρ = ρ * c := by
      rw [← hc]
      exact (Commute.self_pow ρ _).symm.eq
    have hcr : c = r * t := by rw [← hrc, mul_assoc, ht2, mul_one]
    have h1 : r * ρ⁻¹ * r⁻¹ = ρ := by
      have h0 : c * ρ * c⁻¹ = ρ := by rw [hcomm]; group
      rw [hcr] at h0
      calc r * ρ⁻¹ * r⁻¹ = r * (t * ρ * t⁻¹) * r⁻¹ := by rw [hinv1]
        _ = r * t * ρ * (r * t)⁻¹ := by group
        _ = ρ := h0
    have h2 : ρ⁻¹ = r * ρ * r⁻¹ := by
      calc ρ⁻¹ = (r * ρ⁻¹ * r⁻¹)⁻¹ := by rw [h1]
        _ = r * ρ * r⁻¹ := by group
    have h3 : ρ ^ 2 = r⁻¹ * (ρ⁻¹ * r * ρ) := by
      rw [h2, _root_.sq]
      group
    have h4 : ρ⁻¹ * r * ρ ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (hTN (T.inv_mem hρT)) r).mp hr
      rwa [inv_inv] at this
    exact absurd (by rw [show (2 : ℕ) ^ 1 = 2 by norm_num, h3]; exact R.mul_mem (R.inv_mem hr) h4)
      (hmin 1 (by omega))

@[expose] def AllTypeTwo (K : Subgroup G) (z : G) : Prop :=
  ∀ J ∈ CoreAssembly.conjClass K, ∀ u w : G, IsUniqueInvolution J u →
    (∃ x : G, x * z * x⁻¹ = w) → w ≠ u → w * u = u * w → ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ J → Q ≤ Subgroup.centralizer ({w} : Set G) → Nat.card Q ≤ 2

variable {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}

theorem isQuatSub_of_mem_rSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hK : IsClassicalMember p f K z)
    {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K)) : IsQuatSub R := by
  obtain ⟨J, hJ, P, rfl⟩ := hR
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J hJ
  obtain ⟨r, hr, ⟨e⟩⟩ := quaternion_sylow_of_isClassicalMember hp hq (hK.conj g) P
  exact ⟨r - 2, by omega,
    ⟨(Subgroup.equivMapOfInjective _ _ (conjSub g K).subtype_injective).symm.trans e⟩⟩

theorem mem_sup_of_mem_normalizer_of_allTypeTwo (ht : S19R.TightStd p f K z)
    (hA : AllTypeTwo K z) {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K))
    (hRK : R ≤ K) {T : Subgroup G} (hT2 : IsPGroup 2 T) (hRT : R ≤ T)
    (hTN : T ≤ Subgroup.normalizer (R : Set G)) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    {g : G} (htT : g * z * g⁻¹ ∈ T) (htz : g * z * g⁻¹ ≠ z) {h : G} (hsT : h * z * h⁻¹ ∈ T)
    (hsN : h * z * h⁻¹ ∈
      Subgroup.normalizer ((R ⊔ Subgroup.zpowers (g * z * g⁻¹) : Subgroup G) : Set G)) :
    h * z * h⁻¹ ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹) := by
  have htb := ht.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hU := uniqueInvolutionNormal_of_tight htb
  have hconj2 : ∀ x : G, x * z * x⁻¹ * (x * z * x⁻¹) = 1 := fun x => by
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hI.sq]; group
  have hconj1 : ∀ x : G, x * z * x⁻¹ ≠ 1 := fun x h1 => hI.ne_one (by
    calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group)
  set t := g * z * g⁻¹ with htdef
  set s := h * z * h⁻¹ with hsdef
  by_contra hsP
  have ht2 : t * t = 1 := hconj2 g
  have hs2 : s * s = 1 := hconj2 h
  have hzR : IsUniqueInvolution R z := isUniqueInvolution_of_mem_rSet_of_le htb hR hRK
  have hRnc := (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member hR).1
  have hR2 : IsPGroup 2 R := isPGroup_of_mem_rSet hR
  have hord : ∀ y : G, y * y = 1 → y ≠ 1 → orderOf y = 2 := fun y hy hy1 =>
    orderOf_eq_prime (by rw [_root_.sq]; exact hy) hy1
  have htK : t ∉ K := fun htK => htz (hU.2.2.1 t htK (hord t ht2 (hconj1 g)))
  have htR : t ∉ R := fun h1 => htK (hRK h1)
  have htN : t ∈ Subgroup.normalizer (R : Set G) := hTN htT
  have hcommz : ∀ x ∈ T, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hTz hx)
  have hPT : R ⊔ Subgroup.zpowers t ≤ T := sup_le hRT (Subgroup.zpowers_le.mpr htT)
  have hsz : s ≠ z := fun h1 => hsP (by rw [h1]; exact Subgroup.mem_sup_left hzR.mem)
  have hzt : ∀ y ∈ Subgroup.zpowers t, y = 1 ∨ y = t := fun y hy =>
    eq_one_or_eq_of_mem_zpowers_of_mul_self ht2 hy
  have hCRt : ¬ 4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set G)) := by
    have := hA K (CoreAssembly.mem_conjClass_self K) z t hI ⟨g, rfl⟩ htz (hcommz t htT)
      (R ⊓ Subgroup.centralizer ({t} : Set G)) (hR2.to_le inf_le_left) (inf_le_left.trans hRK)
      inf_le_right
    omega
  have hcfg : AscL62.CoreCfg R (Subgroup.zpowers t) z t :=
    { quat := isQuatSub_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member hR
      hz := hzR
      V2 := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, pow_one]; exact hord t ht2 (hconj1 g))
      norm := fun y hy => conjSub_eq_of_mem_normalizer (Subgroup.zpowers_le.mpr htN hy)
      inter := fun y hy hyR => (hzt y hy).resolve_right fun h1 => htR (h1 ▸ hyR)
      ht := ⟨Subgroup.mem_zpowers t, hconj1 g, ht2, fun y hy _ => hzt y hy⟩ }
  obtain ⟨-, hsd⟩ := hcfg.eq_zpowers_and_isSemidihedral hCRt
  obtain ⟨a, b, M, hsdd⟩ := exists_sdData (hT2.to_le hPT) hsd
  have hM := hsdd.M_pos
  have ha2 : a * a ∈ R := mul_self_mem_of_mem_sup_zpowers ht2 htN hsdd.a_mem
  have hza : z = a ^ (4 * (M : ℤ)) := by
    have h4 : a ^ (4 * (M : ℤ)) ∈ R := by
      rw [show 4 * (M : ℤ) = 2 * (2 * M) by ring, zpow_mul, zpow_two]
      exact R.zpow_mem ha2 _
    refine ((hzR.unique _ h4 ?_).resolve_left ?_).symm
    · rw [← zpow_add, hsdd.zpow_eq_one_iff]; exact ⟨1, by ring⟩
    · rw [hsdd.zpow_eq_one_iff]
      rintro ⟨c, hc⟩
      have : (M : ℤ) * (4 - 8 * c) = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0 <;> omega
  have hCRs : ∀ y ∈ R, y * s = s * y → y = 1 ∨ y = z := by
    intro y hyR hys
    have hle := hA K (CoreAssembly.mem_conjClass_self K) z s hI ⟨h, rfl⟩ hsz (hcommz s hsT)
      (R ⊓ Subgroup.centralizer ({s} : Set G)) (hR2.to_le inf_le_left) (inf_le_left.trans hRK)
      inf_le_right
    have hzle : Subgroup.zpowers z ≤ R ⊓ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.zpowers_le]
      exact ⟨hzR.mem, Subgroup.mem_centralizer_singleton_iff.mpr (hcommz s hsT).symm⟩
    have heq : Subgroup.zpowers z = R ⊓ Subgroup.centralizer ({s} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hzle (by
        rw [Nat.card_zpowers, hord z hI.sq hI.ne_one]; exact hle)
    have hy : y ∈ Subgroup.zpowers z := by
      rw [heq]
      exact ⟨hyR, Subgroup.mem_centralizer_singleton_iff.mpr hys⟩
    exact eq_one_or_eq_of_mem_zpowers_of_mul_self hI.sq hy
  have hKs : conjSub h K ∈ CoreAssembly.conjClass K := ⟨h, rfl⟩
  have hIs : IsUniqueInvolution (conjSub h K) s := hI.conj h
  have hkey : ∀ x ∈ R ⊔ Subgroup.zpowers t, x ∉ R → x * s = s * x → False := by
    intro x hxP hxR hxs
    have hx2R : x * x ∈ R := mul_self_mem_of_mem_sup_zpowers ht2 htN hxP
    have hx2s : x * x * s = s * (x * x) := by
      calc x * x * s = x * (x * s) := by group
        _ = x * (s * x) := by rw [hxs]
        _ = s * x * x := by rw [← mul_assoc, hxs]
        _ = s * (x * x) := by group
    obtain ⟨hx2, y, -, hyt⟩ := conj_of_not_mem_of_isSemidihedral hR2 hzR hRnc ht2 htR htN hsd
      hxP hxR (hCRs _ hx2R hx2s)
    have hxzP : x * z ∈ R ⊔ Subgroup.zpowers t :=
      Subgroup.mul_mem _ hxP (Subgroup.mem_sup_left hzR.mem)
    have hxzR : x * z ∉ R := fun h1 => hxR (by
      have := R.mul_mem h1 (R.inv_mem hzR.mem)
      rwa [mul_inv_cancel_right] at this)
    have hxz : x * z = z * x := hcommz x (hPT hxP)
    have hxz2 : x * z * (x * z) = 1 := by
      calc x * z * (x * z) = x * (z * x) * z := by group
        _ = x * (x * z) * z := by rw [← hxz]
        _ = x * x * (z * z) := by group
        _ = 1 := by rw [hx2, hI.sq, one_mul]
    obtain ⟨-, y', -, hy't⟩ := conj_of_not_mem_of_isSemidihedral hR2 hzR hRnc ht2 htR htN hsd
      hxzP hxzR (Or.inl hxz2)
    have hxzs : x * z * s = s * (x * z) := by
      calc x * z * s = x * (z * s) := by group
        _ = x * (s * z) := by rw [(hcommz s hsT).symm]
        _ = s * x * z := by rw [← mul_assoc, hxs]
        _ = s * (x * z) := by group
    have hx1 : x ≠ 1 := fun h1 => hxR (h1 ▸ R.one_mem)
    have hxne : x ≠ z := fun h1 => hxR (h1 ▸ hzR.mem)
    have hVle : Subgroup.zpowers z ≤
        Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
      rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hx2 hw with rfl | rfl
      · group
      · exact hxz
    have hVcard : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z) = 4 := by
      rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hVle (by
          rw [Subgroup.disjoint_def]
          intro w hwx hwz
          rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hx2 hwx with h1 | rfl
          · exact h1
          · rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hI.sq hwz with h1 | h1
            · exact h1
            · exact absurd h1 hxne),
        Nat.card_zpowers, Nat.card_zpowers, hord x hx2 hx1, hord z hI.sq hI.ne_one]
    have hVs : ∀ w ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z, w * s = s * w := by
      intro w hw
      have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤
          Subgroup.centralizer ({s} : Set G) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hxs
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommz s hsT).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    have hVN : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤
        Subgroup.normalizer ((conjSub h K : Subgroup G) : Set G) := fun w hw =>
      mem_normalizer_of_commute_of_tight htb hKs hIs (hVs w hw)
    have hVT : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ T :=
      sup_le (Subgroup.zpowers_le.mpr (hPT hxP)) (Subgroup.zpowers_le.mpr (hRT hzR.mem))
    obtain ⟨Rs, hRs, hRsN⟩ := AscL62.exists_sylow_normalized (hT2.to_le hVT) hVN
    have hVNRs : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤
        Subgroup.normalizer ((Rs : Subgroup G) : Set G) := fun w hw =>
      mem_normalizer_iff_conjSub_eq.mpr (hRsN w hw)
    have hRsR : Rs ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hKs hRs
    have h8 := (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member
      hRsR).2
    obtain ⟨k, hk⟩ := hRs.2.1.exists_card_eq
    have hk3 : 3 ≤ k := by
      by_contra hk3
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h4 : 4 ∣ Nat.card Rs := by
      rw [hk, show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    have hsRs : s ∈ Rs := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥Rs) 2
        (dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4)
      have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
      have huu : (u : G) * u = 1 := by rw [← _root_.sq, ← hu', pow_orderOf_eq_one]
      have hu1 : (u : G) ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hu'
        omega
      have := (hIs.unique u (hRs.1 u.2) huu).resolve_left hu1
      exact this ▸ u.2
    have hfixv : ∀ v ∈ R ⊔ Subgroup.zpowers t, (∃ w : G, w * z * w⁻¹ = v) → v * s = s * v →
        Nat.card ↥(Rs ⊓ Subgroup.centralizer ({v} : Set G)) = 2 := by
      intro v hvP hvz hvs
      have hle := hA (conjSub h K) hKs s v hIs hvz (fun h1 => hsP (h1 ▸ hvP)) hvs
        (Rs ⊓ Subgroup.centralizer ({v} : Set G)) (hRs.2.1.to_le inf_le_left)
        (inf_le_left.trans hRs.1) inf_le_right
      have hne : Rs ⊓ Subgroup.centralizer ({v} : Set G) ≠ ⊥ := by
        intro hbot
        have hmem : s ∈ Rs ⊓ Subgroup.centralizer ({v} : Set G) :=
          ⟨hsRs, Subgroup.mem_centralizer_singleton_iff.mpr hvs.symm⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hconj1 h hmem
      have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
      omega
    refine false_of_card_centralizer_eq_two hVcard hVNRs h4 fun v hv hv1 => ?_
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hxz hv
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hx2 (Subgroup.zpow_mem _
        (Subgroup.mem_zpowers x) i) with hi | hi <;>
      rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hI.sq (Subgroup.zpow_mem _
        (Subgroup.mem_zpowers z) j) with hj | hj <;>
      rw [hi, hj] at hv1 ⊢
    · exact absurd (one_mul 1) hv1
    · rw [one_mul]
      exact hfixv z (Subgroup.mem_sup_left hzR.mem) ⟨1, by group⟩ (hcommz s hsT).symm
    · rw [mul_one]
      exact hfixv x hxP ⟨y * g, by rw [← hyt, htdef]; group⟩ hxs
    · exact hfixv (x * z) hxzP ⟨y' * g, by rw [← hy't, htdef]; group⟩ hxzs
  obtain ⟨x, hxP, hxs, hx1, hxa⟩ := hsdd.exists_centralized hs2 hsN
  by_cases hxR : x ∈ R
  · rcases hCRs x hxR hxs.symm with h1 | h1
    · exact hx1 h1
    · exact hxa (h1.trans hza)
  · exact hkey x hxP hxR hxs.symm

theorem mem_sup_of_allTypeTwo (ht : S19R.TightStd p f K z) (hA : AllTypeTwo K z)
    {R : Subgroup G} (hR : R ∈ RSet (CoreAssembly.conjClass K)) (hRK : R ≤ K)
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hRT : R ≤ T)
    (hTN : T ≤ Subgroup.normalizer (R : Set G)) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    {g : G} (htT : g * z * g⁻¹ ∈ T) (htz : g * z * g⁻¹ ≠ z) {h : G} (hsT : h * z * h⁻¹ ∈ T) :
    h * z * h⁻¹ ∈ R ⊔ Subgroup.zpowers (g * z * g⁻¹) := by
  have hI := isUniqueInvolution_of_tight ht.toTightBranch
  have hconj2 : ∀ x : G, x * z * x⁻¹ * (x * z * x⁻¹) = 1 := fun x => by
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hI.sq]; group
  refine mem_of_mem_normalizer_imp hT2 hTN htT (hconj2 g)
    (X := {x | ∃ w : G, w * z * w⁻¹ = x}) ?_ ?_ ⟨g, rfl⟩ ?_ ⟨h, rfl⟩ hsT
  · rintro x ⟨w, rfl⟩
    exact hconj2 w
  · rintro x ⟨w, rfl⟩ y -
    exact ⟨y * w, by group⟩
  · rintro s ⟨w, rfl⟩ hsT' hsN'
    exact mem_sup_of_mem_normalizer_of_allTypeTwo ht hA hR hRK hT2 hRT hTN hTz htT htz hsT' hsN'

end CFSG.ClassicalInvolution.Disconnected.AschTight
