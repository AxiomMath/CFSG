module

public import CFSG.Certificates.Kernel.EvenBN.Thm49EF6Sound
public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49EF6Sound
public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49EKcard
public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49EModel

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Subgroup Certificates.Thm49E CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.LocalAnalysis.EvenBN.Tits.Model CFSG.KD.T49 CFSG.KS.Raw.Orb

theorem conj_titsZ_eq_self_iff
    {e : Equiv.Perm (Fin 1755)} (he : e ∈ titsD) :
    e * titsZ * e⁻¹ = titsZ ↔ e 0 = 0 := by
  have h1 : e * titsZ * e⁻¹ = titsZ ↔ (⟨e, he⟩ : titsD) ∈ Subgroup.centralizer {titsZD} := by
    rw [Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
    change _ ↔ e * titsZ = titsZ * e
    constructor
    · intro h
      calc e * titsZ = e * titsZ * e⁻¹ * e := by group
        _ = titsZ * e := by rw [h]
    · intro h
      calc e * titsZ * e⁻¹ = titsZ * e * e⁻¹ := by rw [h]
        _ = titsZ := by group
  rw [h1, centralizer_titsZD, Subgroup.mem_subgroupOf, mem_titsH_iff]
  exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

theorem conj_titsZ_eq_iff
    {e e' : Equiv.Perm (Fin 1755)} (he : e ∈ titsD)
    (he' : e' ∈ titsD) : e * titsZ * e⁻¹ = e' * titsZ * e'⁻¹ ↔ e 0 = e' 0 := by
  have hk : e'⁻¹ * e ∈ titsD := mul_mem (inv_mem he') he
  have h := conj_titsZ_eq_self_iff hk
  constructor
  · intro hc
    have h2 : (e'⁻¹ * e) * titsZ * (e'⁻¹ * e)⁻¹ = titsZ := by
      calc (e'⁻¹ * e) * titsZ * (e'⁻¹ * e)⁻¹ = e'⁻¹ * (e * titsZ * e⁻¹) * e' := by group
        _ = titsZ := by rw [hc]; group
    have h3 := h.1 h2
    rw [Equiv.Perm.mul_apply] at h3
    calc e 0 = e' (e'⁻¹ (e 0)) := by simp
      _ = e' 0 := by rw [h3]
  · intro h0
    have h3 : (e'⁻¹ * e) 0 = 0 := by
      rw [Equiv.Perm.mul_apply, h0]
      simp
    have h2 := h.2 h3
    calc e * titsZ * e⁻¹ = e' * ((e'⁻¹ * e) * titsZ * (e'⁻¹ * e)⁻¹) * e'⁻¹ := by group
      _ = e' * titsZ * e'⁻¹ := by rw [h2]

theorem conj_conj_titsZ {c e : Equiv.Perm (Fin 1755)}
    (hc : c ∈ titsA) (hcz : c * titsZ = titsZ * c) (hc0 : c 0 = 0) (he : e ∈ titsD) :
    c * e * c⁻¹ ∈ titsD ∧ (c * e * c⁻¹) 0 = c (e 0) ∧
      c * (e * titsZ * e⁻¹) * c⁻¹ = (c * e * c⁻¹) * titsZ * (c * e * c⁻¹)⁻¹ := by
  refine ⟨titsD_conj_mem hc he, ?_, ?_⟩
  · have : c⁻¹ 0 = 0 := Equiv.Perm.inv_eq_iff_eq.2 hc0.symm
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, this]
  · have hz : titsZ = c * titsZ * c⁻¹ := by
      rw [hcz]
      group
    calc c * (e * titsZ * e⁻¹) * c⁻¹ = (c * e * c⁻¹) * (c * titsZ * c⁻¹) * (c * e * c⁻¹)⁻¹ := by
          group
      _ = (c * e * c⁻¹) * titsZ * (c * e * c⁻¹)⁻¹ := by rw [← hz]

@[expose] noncomputable def titsHZ0 : Subgroup (Equiv.Perm (Fin 1755)) :=
  titsA ⊓ centralizer ({titsZ} : Set (Equiv.Perm (Fin 1755))) ⊓
    MulAction.stabilizer (Equiv.Perm (Fin 1755)) (0 : Fin 1755)

theorem mem_titsHZ0 {c : Equiv.Perm (Fin 1755)} :
    c ∈ titsHZ0 ↔ c ∈ titsA ∧ c * titsZ = titsZ * c ∧ c 0 = 0 := by
  rw [titsHZ0, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

section Data

variable {W : F6W}

theorem prepF (hW : F6OK W) : ∀ j < 4, PR (W.F j) (titsGen j) :=
  fun j hj => prep_of_rep (by rw [← hW.bindF j hj]; exact titsGen_rep hj)

theorem prepFI (hW : F6OK W) :
    ∀ j < 4, PR (W.FI j) (titsGen j)⁻¹ :=
  fun j hj => prep_inv (prepF hW j hj) ((f6K_spec hW.check).permF j hj)

theorem prepD (hW : F6OK W) : ∀ j < 2, PR (W.D j) (titsDGen j) :=
  fun j hj => prep_of_rep (by
    rw [← hW.bindD j hj, ← titsDerived_perm hj]
    exact rep_of_allPermsOK titsChains_check.2.2.2.2.2.2.1 (by rw [titsDerivedArrs_size]; omega))

theorem prepDI (hW : F6OK W) :
    ∀ j < 2, PR (W.DI j) (titsDGen j)⁻¹ :=
  fun j hj => prep_inv (prepD hW j hj) ((f6K_spec hW.check).permD j hj)

theorem prepZ (hW : F6OK W) :
    PR W.Z titsZ :=
  prep_of_rep (by rw [← hW.bindZ]; exact titsZ_rep)

theorem wordIn_titsD_mem (w : List Int) : wordIn 2 titsDGen w ∈ titsD :=
  wordIn_mem (fun _ hj => titsDGen_mem_titsD hj) w

end Data

theorem card_fix_conj (g d : Equiv.Perm (Fin 1755)) :
    (Finset.univ.filter (fun x : Fin 1755 => (d * g * d⁻¹) x = x)).card =
      (Finset.univ.filter (fun x : Fin 1755 => g x = x)).card := by
  have hi1 : ∀ x, d⁻¹ (d x) = x := fun x => Equiv.symm_apply_apply d x
  have hi2 : ∀ x, d (d⁻¹ x) = x := fun x => Equiv.apply_symm_apply d x
  have key : ∀ x : Fin 1755, (d * g * d⁻¹) x = x ↔ g (d⁻¹ x) = d⁻¹ x := by
    intro x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    constructor
    · intro h
      conv_rhs => rw [← h]
      rw [hi1]
    · intro h
      rw [h, hi2]
  refine Finset.card_bij (fun x _ => d⁻¹ x) (fun x hx => ?_) (fun a _ b _ h => d⁻¹.injective h)
    (fun y hy => ⟨d y, ?_, hi1 y⟩)
  · rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, (key x).1 hx.2⟩
  · rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, (key (d y)).2 ?_⟩
    rw [hi1]
    exact hy.2

theorem conj_of_mul {a b c : Equiv.Perm (Fin 1755)} (h : a * b = c * a) : a * b * a⁻¹ = c := by
  rw [h]
  group

theorem fin_zero_eq : (0 : Fin 1755) = ⟨0, by norm_num⟩ := rfl

theorem fin_eq_of_ap {P : Nat} {g : Equiv.Perm (Fin 1755)} (hP : PR P g) {x y : Nat}
    (hx : x < 1755) (h : ap P x = y) : g ⟨x, hx⟩ = ⟨y, by rw [← h]; exact ap_lt hP hx⟩ :=
  Fin.ext (by rw [← ap_eq' hP hx, h])

structure F6Perm (W : F6W) : Prop where
  z_sq : titsZ * titsZ = 1
  zp_comm : zpHat * titsZ = titsZ * zpHat
  zp_ne : zpHat ≠ titsZ
  e_mem : wordIn 2 titsDGen W.ew ∈ titsD
  e_conj : wordIn 2 titsDGen W.ew * titsZ * (wordIn 2 titsDGen W.ew)⁻¹ = zpHat
  yp_lt : W.yp < 1755
  e_zero : ((wordIn 2 titsDGen W.ew 0 : Fin 1755) : Nat) = W.yp
  y0_z : y0Hat * titsZ * y0Hat⁻¹ = zpHat
  y0_zp : y0Hat * zpHat * y0Hat⁻¹ = titsZ
  fix_z : ∀ x : Fin 1755, (x : Nat) ∈ W.fz ↔ titsZ x = x
  len_z : W.fz.length = (Finset.univ.filter (fun x : Fin 1755 => titsZ x = x)).card
  len_zz : W.fzz.length =
    (Finset.univ.filter (fun x : Fin 1755 => (titsZ * zpHat) x = x)).card
  u1_mem : wordIn 4 titsGen u1Word ∈ titsHZ0
  u2_mem : wordIn 4 titsGen u2Word ∈ titsHZ0
  r2_lt : W.r2 < 1755
  e1_zero : ((wordIn 2 titsDGen W.e1w 0 : Fin 1755) : Nat) = W.r2
  f_rel : titsZ * (wordIn 2 titsDGen W.e1w * titsZ * (wordIn 2 titsDGen W.e1w)⁻¹) =
    wordIn 2 titsDGen W.fw * titsZ * (wordIn 2 titsDGen W.fw)⁻¹
  reach1 : ∀ y, bitK (orbMask W.o1 (setK 0 W.yp)) y = true →
    ∃ c ∈ titsHZ0, ((c ⟨W.yp, yp_lt⟩ : Fin 1755) : Nat) = y
  reach2 : ∀ y, bitK (orbMask W.o2 (setK 0 W.r2)) y = true →
    ∃ c ∈ titsHZ0, ((c ⟨W.r2, r2_lt⟩ : Fin 1755) : Nat) = y

theorem f6Perm_of {W : F6W}
    (hW : F6OK W) : F6Perm W := by
  have S := f6K_spec hW.check
  have C := S.core
  have hF := prepF hW
  have hFI := prepFI hW
  have hD := prepD hW
  have hDI := prepDI hW
  have hZ := prepZ hW
  have hzp : PR (wd W.F W.FI zpWord) zpHat := prep_wd hF hFI S.lzp
  have hy0 : PR (wd W.F W.FI y0Word) y0Hat := prep_wd hF hFI S.ly0
  have hu1 : PR (wd W.F W.FI u1Word) (wordIn 4 titsGen u1Word) := prep_wd hF hFI S.lu1
  have hu2 : PR (wd W.F W.FI u2Word) (wordIn 4 titsGen u2Word) := prep_wd hF hFI S.lu2
  have he : PR (wd W.D W.DI W.ew) (wordIn 2 titsDGen W.ew) := prep_wd hD hDI S.le
  have he1 : PR (wd W.D W.DI W.e1w) (wordIn 2 titsDGen W.e1w) := prep_wd hD hDI S.le1
  have he1i : PR (wd W.D W.DI W.e1iw) (wordIn 2 titsDGen W.e1iw) := prep_wd hD hDI S.le1i
  have hf : PR (wd W.D W.DI W.fw) (wordIn 2 titsDGen W.fw) := prep_wd hD hDI S.lf
  have h0 : (0 : Nat) < 1755 := by norm_num
  have hyp : W.yp < 1755 := by
    rw [← C.e0]
    exact ap_lt he h0
  have hr2 : W.r2 < 1755 := by
    rw [← C.e10]
    exact ap_lt he1 h0
  have hum : ∀ {P : Nat} {u : Equiv.Perm (Fin 1755)} {w : List Int}, PR P u →
      u = wordIn 4 titsGen w → pmul P W.Z = pmul W.Z P → ap P 0 = 0 → u ∈ titsHZ0 := by
    intro P u w hP hu hc h00
    rw [mem_titsHZ0]
    refine ⟨hu ▸ wordIn_mem_titsA' w, mul_eq_of hP hZ hZ hP hc, ?_⟩
    rw [fin_zero_eq, fin_eq_of_ap hP h0 h00]
  have hu1K := hum hu1 rfl C.u1Z C.u10
  have hu2K := hum hu2 rfl C.u2Z C.u20
  have he1i' : wordIn 2 titsDGen W.e1iw = (wordIn 2 titsDGen W.e1w)⁻¹ :=
    (eq_inv_of_mul_eq_one_right (eq_of_prep (prep_pmul he1 he1i) prep_idP C.e1inv))
  have hreach : ∀ (rs : List Nat) (r : Nat) (hr : r < 1755), orbOK (wd W.F W.FI u1Word)
      (wd W.F W.FI u2Word) rs (setK 0 r) = true → ∀ y, bitK (orbMask rs (setK 0 r)) y = true →
      ∃ c ∈ titsHZ0, ((c ⟨r, hr⟩ : Fin 1755) : Nat) = y := by
    intro rs r hr hok
    refine orb_reach hu1 hu2 hu1K hu2K ⟨r, hr⟩ rs _ hok (fun t ht => ?_)
    rw [bitK_root] at ht
    exact ⟨1, one_mem _, by rw [ht]; rfl⟩
  refine
    { z_sq := ?_
      zp_comm := mul_eq_of hzp hZ hZ hzp C.zpComm
      zp_ne := fun h => C.q0ne (by rw [ap_eq' hzp C.q0lt, ap_eq' hZ C.q0lt, h])
      e_mem := wordIn_titsD_mem _
      e_conj := conj_of_mul (mul_eq_of he hZ hzp he C.eZ)
      yp_lt := hyp
      e_zero := by rw [fin_zero_eq, ← ap_eq' he h0, C.e0]
      y0_z := conj_of_mul (mul_eq_of hy0 hZ hzp hy0 C.y0z)
      y0_zp := conj_of_mul (mul_eq_of hy0 hzp hZ hy0 C.y0zp)
      fix_z := mem_fixed hZ C.fixZ
      len_z := length_fixed hZ C.fixZ
      len_zz := length_fixed (prep_pmul hZ hzp) C.fixZZ
      u1_mem := hu1K
      u2_mem := hu2K
      r2_lt := hr2
      e1_zero := by rw [fin_zero_eq, ← ap_eq' he1 h0, C.e10]
      f_rel := ?_
      reach1 := hreach W.o1 W.yp hyp C.o1ok
      reach2 := hreach W.o2 W.r2 hr2 C.o2ok }
  · have hZi : PR W.Z titsZ⁻¹ := prep_inv hZ S.permZ
    have e : titsZ = titsZ⁻¹ := eq_of_prep hZ hZi rfl
    nth_rewrite 2 [e]
    exact mul_inv_cancel _
  · have h := eq_of_prep (prep_pmul (prep_pmul (prep_pmul hZ (prep_pmul he1 hZ)) he1i) hf)
      (prep_pmul hf hZ) C.fRel
    rw [he1i'] at h
    calc titsZ * (wordIn 2 titsDGen W.e1w * titsZ * (wordIn 2 titsDGen W.e1w)⁻¹) =
        titsZ * (wordIn 2 titsDGen W.e1w * titsZ) * (wordIn 2 titsDGen W.e1w)⁻¹ *
          wordIn 2 titsDGen W.fw * (wordIn 2 titsDGen W.fw)⁻¹ := by group
      _ = wordIn 2 titsDGen W.fw * titsZ * (wordIn 2 titsDGen W.fw)⁻¹ := by rw [h]

theorem f6Facts_of_k
    {W : F6W} (hW : F6OK W) : F6Facts zpHat y0Hat := by
  have P := f6Perm_of hW
  have C := (f6K_spec hW.check).core
  have hzD : titsZ ∈ titsD := titsZ_mem_titsD
  refine ⟨P.z_sq, titsD_le_titsA hzD, wordIn_mem_titsA' _, ⟨_, P.e_mem, P.e_conj⟩, P.zp_ne,
    P.zp_comm.symm, ?_, wordIn_mem_titsA' _, P.y0_z, P.y0_zp, ?_⟩
  · rintro ⟨d, -, hdz⟩
    apply C.lenNe
    rw [P.len_z, P.len_zz, ← hdz, card_fix_conj]
  · intro a b ha hb hab hcomm hnl
    obtain ⟨d, hd, rfl⟩ := ha
    obtain ⟨d', hd', rfl⟩ := hb
    obtain ⟨e, rfl⟩ : ∃ e, d' = d * e := ⟨d⁻¹ * d', by group⟩
    have heD : e ∈ titsD := by
      have := mul_mem (inv_mem hd) hd'
      rwa [inv_mul_cancel_left] at this
    have hb' : d * e * titsZ * (d * e)⁻¹ = d * (e * titsZ * e⁻¹) * d⁻¹ := by group
    have hc' : titsZ * (e * titsZ * e⁻¹) = (e * titsZ * e⁻¹) * titsZ := by
      have h := hcomm
      rw [hb'] at h
      calc titsZ * (e * titsZ * e⁻¹) =
          d⁻¹ * (d * titsZ * d⁻¹ * (d * (e * titsZ * e⁻¹) * d⁻¹)) * d := by group
        _ = d⁻¹ * (d * (e * titsZ * e⁻¹) * d⁻¹ * (d * titsZ * d⁻¹)) * d := by rw [h]
        _ = (e * titsZ * e⁻¹) * titsZ := by group
    have hfix : titsZ (e 0) = e 0 := by
      have h1 : (titsZ * e) * titsZ * (titsZ * e)⁻¹ = e * titsZ * e⁻¹ := by
        calc (titsZ * e) * titsZ * (titsZ * e)⁻¹ = titsZ * (e * titsZ * e⁻¹) * titsZ⁻¹ := by
              group
          _ = (e * titsZ * e⁻¹) * titsZ * titsZ⁻¹ := by rw [hc']
          _ = e * titsZ * e⁻¹ := by group
      have := (conj_titsZ_eq_iff (mul_mem hzD heD) heD).1 h1
      rwa [Equiv.Perm.mul_apply] at this
    have hy0 : e 0 ≠ 0 := by
      intro h0
      have h2 := (conj_titsZ_eq_self_iff heD).2 h0
      apply hab
      rw [hb', h2]
    have e2 : ∀ {c : Equiv.Perm (Fin 1755)}, c * titsZ = titsZ * c → c * titsZ * c⁻¹ = titsZ := by
      intro c hcz
      rw [hcz]
      group
    rcases C.cover _ ((P.fix_z _).2 hfix) with h | h | h
    · exact absurd (Fin.ext h) hy0
    · obtain ⟨c, hc, hcy⟩ := P.reach1 _ h
      obtain ⟨hcA, hcz, hc0⟩ := mem_titsHZ0.1 hc
      obtain ⟨hgD, hg0, hgc⟩ := conj_conj_titsZ hcA hcz hc0 P.e_mem
      have hg0' : (c * wordIn 2 titsDGen W.ew * c⁻¹) 0 = e 0 := by
        rw [hg0, show wordIn 2 titsDGen W.ew 0 = ⟨W.yp, P.yp_lt⟩ from Fin.ext P.e_zero]
        exact Fin.ext hcy
      have hbb : e * titsZ * e⁻¹ = c * zpHat * c⁻¹ := by
        rw [← P.e_conj, hgc]
        exact ((conj_titsZ_eq_iff hgD heD).2 hg0').symm
      have e1 : c⁻¹ * titsZ * c = titsZ := by
        calc c⁻¹ * titsZ * c = c⁻¹ * (titsZ * c) := by group
          _ = c⁻¹ * (c * titsZ) := by rw [hcz]
          _ = titsZ := by group
      refine ⟨d * c * y0Hat * c⁻¹ * d⁻¹, ?_, ?_, ?_⟩
      · have hdA := titsD_le_titsA hd
        exact mul_mem (mul_mem (mul_mem (mul_mem hdA hcA) (wordIn_mem_titsA' _)) (inv_mem hcA))
          (inv_mem hdA)
      · calc d * c * y0Hat * c⁻¹ * d⁻¹ * (d * titsZ * d⁻¹) * (d * c * y0Hat * c⁻¹ * d⁻¹)⁻¹ =
            d * c * (y0Hat * (c⁻¹ * titsZ * c) * y0Hat⁻¹) * c⁻¹ * d⁻¹ := by group
          _ = d * c * (y0Hat * titsZ * y0Hat⁻¹) * c⁻¹ * d⁻¹ := by rw [e1]
          _ = d * (c * zpHat * c⁻¹) * d⁻¹ := by rw [P.y0_z]; group
          _ = d * e * titsZ * (d * e)⁻¹ := by rw [← hbb]; group
      · calc d * c * y0Hat * c⁻¹ * d⁻¹ * (d * e * titsZ * (d * e)⁻¹) *
              (d * c * y0Hat * c⁻¹ * d⁻¹)⁻¹ =
            d * c * y0Hat * c⁻¹ * d⁻¹ * (d * (c * zpHat * c⁻¹) * d⁻¹) *
              (d * c * y0Hat * c⁻¹ * d⁻¹)⁻¹ := by rw [hb', hbb]
          _ = d * c * (y0Hat * zpHat * y0Hat⁻¹) * c⁻¹ * d⁻¹ := by group
          _ = d * (c * titsZ * c⁻¹) * d⁻¹ := by rw [P.y0_zp]; group
          _ = d * titsZ * d⁻¹ := by rw [e2 hcz]
    · exfalso
      obtain ⟨c, hc, hcy⟩ := P.reach2 _ h
      obtain ⟨hcA, hcz, hc0⟩ := mem_titsHZ0.1 hc
      obtain ⟨hgD, hg0, hgc⟩ := conj_conj_titsZ hcA hcz hc0 (wordIn_titsD_mem W.e1w)
      have hg0' : (c * wordIn 2 titsDGen W.e1w * c⁻¹) 0 = e 0 := by
        rw [hg0, show wordIn 2 titsDGen W.e1w 0 = ⟨W.r2, P.r2_lt⟩ from Fin.ext P.e1_zero]
        exact Fin.ext hcy
      have hbb : e * titsZ * e⁻¹ =
          c * (wordIn 2 titsDGen W.e1w * titsZ * (wordIn 2 titsDGen W.e1w)⁻¹) * c⁻¹ := by
        rw [hgc]
        exact ((conj_titsZ_eq_iff hgD heD).2 hg0').symm
      obtain ⟨hfD, -, hfc⟩ := conj_conj_titsZ hcA hcz hc0 (wordIn_titsD_mem W.fw)
      apply hnl
      refine ⟨d * (c * wordIn 2 titsDGen W.fw * c⁻¹), mul_mem hd hfD, ?_⟩
      symm
      calc d * titsZ * d⁻¹ * (d * e * titsZ * (d * e)⁻¹) =
          d * (titsZ * (e * titsZ * e⁻¹)) * d⁻¹ := by group
        _ = d * (titsZ * (c * (wordIn 2 titsDGen W.e1w * titsZ * (wordIn 2 titsDGen W.e1w)⁻¹) *
            c⁻¹)) * d⁻¹ := by rw [hbb]
        _ = d * ((c * titsZ * c⁻¹) * (c * (wordIn 2 titsDGen W.e1w * titsZ *
            (wordIn 2 titsDGen W.e1w)⁻¹) * c⁻¹)) * d⁻¹ := by rw [e2 hcz]
        _ = d * (c * (titsZ * (wordIn 2 titsDGen W.e1w * titsZ * (wordIn 2 titsDGen W.e1w)⁻¹)) *
            c⁻¹) * d⁻¹ := by group
        _ = d * (c * (wordIn 2 titsDGen W.fw * titsZ * (wordIn 2 titsDGen W.fw)⁻¹) * c⁻¹) *
            d⁻¹ := by rw [P.f_rel]
        _ = d * ((c * wordIn 2 titsDGen W.fw * c⁻¹) * titsZ *
            (c * wordIn 2 titsDGen W.fw * c⁻¹)⁻¹) * d⁻¹ := by rw [hfc]
        _ = d * (c * wordIn 2 titsDGen W.fw * c⁻¹) * titsZ *
            (d * (c * wordIn 2 titsDGen W.fw * c⁻¹))⁻¹ := by group

theorem kcard_of_k
    {W : F6W} (hW : F6OK W) :
    Nat.card ↥(titsA ⊓ centralizer ({titsZ} : Set (Equiv.Perm (Fin 1755))) ⊓
      centralizer ({zpHat} : Set (Equiv.Perm (Fin 1755)))) ≤ 256 := by
  have P := f6Perm_of hW
  have C := (f6K_spec hW.check).core
  have hA : Nat.card ↥(titsA ⊓ centralizer ({titsZ} : Set (Equiv.Perm (Fin 1755)))) ≤ 20480 := by
    have hX := ncard_titsA_class_titsZ
    have hfin := Set.toFinite {y | ∃ a ∈ titsA, a * titsZ * a⁻¹ = y}
    have h := card_mul_card_inf_centralizer_le titsA titsZ hfin.toFinset (fun s hs => by
      rw [Set.Finite.mem_toFinset] at hs
      exact hs)
    rw [← Set.ncard_eq_toFinset_card _ hfin, hX, card_titsA] at h
    omega
  have hnd : (W.yp :: W.o1.map recY).Nodup := by
    have := orb_nodup W.o1 (setK 0 W.yp) [W.yp] C.o1ok (List.nodup_singleton _) (by
      intro y hy
      rw [List.mem_singleton] at hy
      rw [bitK_root]
      exact hy)
    simpa using this
  have hlen : (W.yp :: W.o1.map recY).length = 80 := by
    rw [List.length_cons, List.length_map, C.o1len]
  have hreachL : ∀ y ∈ W.yp :: W.o1.map recY,
      ∃ c ∈ titsHZ0, ((c ⟨W.yp, P.yp_lt⟩ : Fin 1755) : Nat) = y := by
    intro y hy
    apply P.reach1
    rcases List.mem_cons.1 hy with rfl | hy
    · exact orbMask_mono _ _ _ ((bitK_root _ _).2 rfl)
    · exact orbMask_mem _ _ _ hy
  choose! cf hcfK hcfy using hreachL
  have hlab : ∀ y ∈ W.yp :: W.o1.map recY, ∃ g ∈ titsD, ((g 0 : Fin 1755) : Nat) = y ∧
      cf y * zpHat * (cf y)⁻¹ = g * titsZ * g⁻¹ := by
    intro y hy
    obtain ⟨hcA, hcz, hc0⟩ := mem_titsHZ0.1 (hcfK y hy)
    obtain ⟨hgD, hg0, hgc⟩ := conj_conj_titsZ hcA hcz hc0 P.e_mem
    refine ⟨_, hgD, ?_, by rw [← P.e_conj, hgc]⟩
    rw [hg0, show wordIn 2 titsDGen W.ew 0 = ⟨W.yp, P.yp_lt⟩ from Fin.ext P.e_zero]
    exact hcfy y hy
  have hinj : ∀ y ∈ W.yp :: W.o1.map recY, ∀ y' ∈ W.yp :: W.o1.map recY,
      cf y * zpHat * (cf y)⁻¹ = cf y' * zpHat * (cf y')⁻¹ → y = y' := by
    intro y hy y' hy' he
    obtain ⟨g, hg, hg0, hgc⟩ := hlab y hy
    obtain ⟨g', hg', hg0', hgc'⟩ := hlab y' hy'
    rw [hgc, hgc'] at he
    rw [← hg0, ← hg0', (conj_titsZ_eq_iff hg hg').1 he]
  have hS : ((W.yp :: W.o1.map recY).map fun y => cf y * zpHat * (cf y)⁻¹).toFinset.card = 80 := by
    rw [List.toFinset_card_of_nodup (hnd.map_on hinj), List.length_map, hlen]
  have hB := card_mul_card_inf_centralizer_le
    (titsA ⊓ centralizer ({titsZ} : Set (Equiv.Perm (Fin 1755)))) zpHat
    ((W.yp :: W.o1.map recY).map fun y => cf y * zpHat * (cf y)⁻¹).toFinset (fun s hs => by
      rw [List.mem_toFinset, List.mem_map] at hs
      obtain ⟨y, hy, rfl⟩ := hs
      obtain ⟨hcA, hcz, -⟩ := mem_titsHZ0.1 (hcfK y hy)
      exact ⟨cf y, Subgroup.mem_inf.2 ⟨hcA, Subgroup.mem_centralizer_singleton_iff.2 hcz⟩, rfl⟩)
  rw [hS] at hB
  omega

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

end
