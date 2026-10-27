module

public import CFSG.LargeExtraspecial.AS35QTSChart
public import CFSG.LargeExtraspecial.AS35EResid

public section

namespace CFSG.LargeExtraspecial.AS35QTS

open Subgroup

variable {G : Type} [Group G] (S : Setting G)

@[expose] def lineSet (d c : G) : Set G := {y | IsConj S.z y ∧ y * d = d * y ∧ y * c = c * y}

theorem z_mem_M : S.z ∈ S.M := S.zM.2

theorem exists_t [Finite G] (hS : S.SixHyp) : ∃ t ∈ S.M, IsConj S.z t ∧ t ≠ S.z := by
  obtain ⟨t, ht⟩ := S.DSet_nonempty hS.sixFour hS.hSet_nonempty
  exact ⟨t, S.mem_M_of_mem_ESet hS.sixFour ht.1, S.isConj_of_mem_ESet ht.1,
    S.ne_z_of_mem_ESet ht.1⟩

theorem mem_M_of_mem_lineSet {t y : G} (hy : y ∈ lineSet S S.z t) : y ∈ S.M :=
  S.mem_M_iff.mpr hy.2.1


namespace Chart

variable {S} [Finite G] (T : Chart S)

theorem dl_nodup : dl.Nodup :=
  List.nodup_cons.mpr ⟨tau0_not_mem_sl, qts_lists.2.2.2⟩

theorem mem_dl_codes {c : Cd} (hc : c ∈ dl) : c ∈ codes := by
  rcases mem_dl.mp hc with rfl | h
  · exact tau0_mem
  · exact (mem_il.mp (mem_sl.mp h).1).1

theorem exists_th_eq (hS : S.SixHyp) {c : Cd} (hc : c ∈ sl) :
    ∃ x ∈ S.M, IsConj S.z x ∧ T.th x = c := by
  obtain ⟨t, htM, htz, htne⟩ := exists_t S hS
  have hts := T.th_mem_sl hS.weak htM htz htne
  obtain ⟨x, hxM, rfl⟩ := T.th_surj c (mem_il.mp (mem_sl.mp hc).1).1
  obtain ⟨m, hm, rfl⟩ := T.exists_conj_of_mem_sl htM hts hxM hc
  exact ⟨m * t * m⁻¹, hxM, htz.trans (isConj_iff.mpr ⟨m, rfl⟩), rfl⟩

theorem mem_D_iff (hS : S.SixHyp) {x : G} (hx : x ∈ S.M) : IsConj S.z x ↔ T.th x ∈ dl := by
  constructor
  · intro hxz
    by_cases hxe : x = S.z
    · rw [hxe, T.th_z]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (T.th_mem_sl hS.weak hx hxz hxe)
  · intro h
    rcases mem_dl.mp h with h | h
    · rw [← T.th_z] at h
      rw [T.th_injOn x hx S.z S.zM.2 h]
    · obtain ⟨y, hyM, hyz, hy⟩ := T.exists_th_eq hS h
      rwa [← T.th_injOn y hyM x hx hy]

theorem image_DM (hS : S.SixHyp) :
    T.th '' {x | IsConj S.z x ∧ x ∈ S.M} = {c | c ∈ dl} := by
  ext c
  constructor
  · rintro ⟨x, ⟨hxz, hxM⟩, rfl⟩
    exact (T.mem_D_iff hS hxM).mp hxz
  · intro hc
    obtain ⟨x, hxM, rfl⟩ := T.th_surj c (mem_dl_codes hc)
    exact ⟨x, ⟨(T.mem_D_iff hS hxM).mpr hc, hxM⟩, rfl⟩

omit [Finite G] in
theorem ncard_list {l : List Cd} (hl : l.Nodup) : {c | c ∈ l}.ncard = l.length := by
  classical
  have e : {c | c ∈ l} = ↑l.toFinset := by
    ext c
    simp
  rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hl]

include T in
theorem ncard_DM (hS : S.SixHyp) : {x | IsConj S.z x ∧ x ∈ S.M}.ncard = 37 := by
  have hinj : Set.InjOn T.th {x | IsConj S.z x ∧ x ∈ S.M} :=
    fun x hx y hy h => T.th_injOn x hx.2 y hy.2 h
  rw [← hinj.ncard_image, T.image_DM hS, ncard_list dl_nodup, dl, List.length_cons,
    qts_lists.2.2.1]

theorem th_mem_lineIn_iff (hS : S.SixHyp) {t y : G} (ht : t ∈ S.M) (hy : y ∈ S.M) :
    y ∈ lineSet S S.z t ↔ T.th y ∈ lineIn dl (T.th t) := by
  rw [mem_lineIn]
  constructor
  · rintro ⟨hyz, -, hyt⟩
    exact ⟨(T.mem_D_iff hS hy).mp hyz, ((T.th_comm ht hy).mp hyt.symm)⟩
  · rintro ⟨hyd, hyt⟩
    exact ⟨(T.mem_D_iff hS hy).mpr hyd, S.mem_M_iff.mp hy, ((T.th_comm ht hy).mpr hyt).symm⟩

theorem image_lineSet (hS : S.SixHyp) {t : G} (ht : t ∈ S.M) :
    T.th '' lineSet S S.z t = {c | c ∈ lineIn dl (T.th t)} := by
  ext c
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (T.th_mem_lineIn_iff hS ht (mem_M_of_mem_lineSet S hy)).mp hy
  · intro hc
    obtain ⟨y, hyM, rfl⟩ := T.th_surj c (mem_dl_codes (mem_lineIn.mp hc).1)
    exact ⟨y, (T.th_mem_lineIn_iff hS ht hyM).mpr hc, rfl⟩

include T in
theorem ncard_lineSet (hS : S.SixHyp) {t : G} (ht : t ∈ S.M) (htz : IsConj S.z t)
    (hne : t ≠ S.z) : (lineSet S S.z t).ncard = 5 := by
  have hinj : Set.InjOn T.th (lineSet S S.z t) := fun x hx y hy h =>
    T.th_injOn x (mem_M_of_mem_lineSet S hx) y (mem_M_of_mem_lineSet S hy) h
  rw [← hinj.ncard_image, T.image_lineSet hS ht,
    ncard_list (show (lineIn dl (T.th t)).Nodup from dl_nodup.filter _)]
  exact qts_line_parts.1 _ (T.th_mem_sl hS.weak ht htz hne)

include T in
theorem commute_of_mem_lineSet (hS : S.SixHyp) {t : G} (ht : t ∈ S.M) (htz : IsConj S.z t)
    (hne : t ≠ S.z) {a b : G} (ha : a ∈ lineSet S S.z t) (hb : b ∈ lineSet S S.z t) :
    a * b = b * a := by
  have haM := mem_M_of_mem_lineSet S ha
  have hbM := mem_M_of_mem_lineSet S hb
  exact (T.th_comm haM hbM).mpr (qts_line_parts.2.1 _ (T.th_mem_sl hS.weak ht htz hne) _
    ((T.th_mem_lineIn_iff hS ht haM).mp ha) _ ((T.th_mem_lineIn_iff hS ht hbM).mp hb))

include T in
theorem lineSet_eq (hS : S.SixHyp) {t p : G} (ht : t ∈ S.M) (htz : IsConj S.z t)
    (hne : t ≠ S.z) (hp : p ∈ lineSet S S.z t) (hpz : p ≠ S.z) :
    lineSet S S.z p = lineSet S S.z t := by
  have hpM := mem_M_of_mem_lineSet S hp
  have hts := T.th_mem_sl hS.weak ht htz hne
  have hps := T.th_mem_sl hS.weak hpM hp.1 hpz
  have htp : mulC (T.th t) (T.th p) = mulC (T.th p) (T.th t) := (T.th_comm ht hpM).mp hp.2.2.symm
  ext y
  constructor
  · intro hy
    have hyM := mem_M_of_mem_lineSet S hy
    rw [T.th_mem_lineIn_iff hS ht hyM]
    rw [T.th_mem_lineIn_iff hS hpM hyM, mem_lineIn] at hy
    refine mem_lineIn.mpr ⟨hy.1, ?_⟩
    rcases mem_dl.mp hy.1 with hy' | hy'
    · rw [hy', ← T.th_z, ← T.th_mul t ht S.z (z_mem_M S), ← T.th_mul S.z (z_mem_M S) t ht]
      exact congrArg T.th (S.mem_M_iff.mp ht)
    · exact ((qts_line_parts.2.2.1 _ hts _ hps htp _ hy').mpr hy.2)
  · intro hy
    have hyM := mem_M_of_mem_lineSet S hy
    rw [T.th_mem_lineIn_iff hS hpM hyM]
    rw [T.th_mem_lineIn_iff hS ht hyM, mem_lineIn] at hy
    refine mem_lineIn.mpr ⟨hy.1, ?_⟩
    rcases mem_dl.mp hy.1 with hy' | hy'
    · rw [hy', ← T.th_z, ← T.th_mul p hpM S.z (z_mem_M S), ← T.th_mul S.z (z_mem_M S) p hpM]
      exact congrArg T.th (S.mem_M_iff.mp hpM)
    · exact ((qts_line_parts.2.2.1 _ hts _ hps htp _ hy').mp hy.2)

include T in
theorem eq_of_mul_eq (hS : S.SixHyp) {t : G} (ht : t ∈ S.M) (htz : IsConj S.z t)
    (hne : t ≠ S.z) {a b a' b' : G} (ha : a ∈ lineSet S S.z t) (hb : b ∈ lineSet S S.z t)
    (ha' : a' ∈ lineSet S S.z t) (hb' : b' ∈ lineSet S S.z t) (hab : a ≠ b) (hab' : a' ≠ b')
    (he : a * b = a' * b') : (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  have haM := mem_M_of_mem_lineSet S ha
  have hbM := mem_M_of_mem_lineSet S hb
  have ha'M := mem_M_of_mem_lineSet S ha'
  have hb'M := mem_M_of_mem_lineSet S hb'
  have h := qts_line_parts.2.2.2.1 _ (T.th_mem_sl hS.weak ht htz hne) _
    ((T.th_mem_lineIn_iff hS ht haM).mp ha) _ ((T.th_mem_lineIn_iff hS ht hbM).mp hb) _
    ((T.th_mem_lineIn_iff hS ht ha'M).mp ha') _ ((T.th_mem_lineIn_iff hS ht hb'M).mp hb')
    (fun h => hab (T.th_injOn a haM b hbM h)) (fun h => hab' (T.th_injOn a' ha'M b' hb'M h))
    (by rw [← T.th_mul _ haM _ hbM, ← T.th_mul _ ha'M _ hb'M, he])
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨T.th_injOn _ haM _ ha'M h1, T.th_injOn _ hbM _ hb'M h2⟩
  · exact Or.inr ⟨T.th_injOn _ haM _ hb'M h1, T.th_injOn _ hbM _ ha'M h2⟩

include T in
theorem orderOf_mul_dvd (hS : S.SixHyp) {a b : G} (ha : a ∈ S.M) (hb : b ∈ S.M)
    (haz : IsConj S.z a) (hbz : IsConj S.z b) :
    (a * b) ^ 2 = 1 ∨ (a * b) ^ 3 = 1 := by
  have hab := S.M.mul_mem ha hb
  rcases qts_ord _ _ ((T.mem_D_iff hS ha).mp haz) ((T.mem_D_iff hS hb).mp hbz) with h | h
  · left
    rw [pow_two]
    apply (T.th_eq_e0_iff (S.M.mul_mem hab hab)).mp
    rw [T.th_mul _ hab _ hab, T.th_mul _ ha _ hb]
    exact h
  · right
    rw [pow_succ, pow_two]
    apply (T.th_eq_e0_iff (S.M.mul_mem (S.M.mul_mem hab hab) hab)).mp
    rw [T.th_mul _ (S.M.mul_mem hab hab) _ hab, T.th_mul _ hab _ hab, T.th_mul _ ha _ hb]
    exact h

include T in
theorem not_isConj_mul (hS : S.SixHyp) {t : G} (ht : t ∈ S.M) (htz : IsConj S.z t)
    (hne : t ≠ S.z) : ¬ IsConj S.z (S.z * t) := by
  intro h
  have hzt := S.M.mul_mem (z_mem_M S) ht
  have h1 := (T.mem_D_iff hS hzt).mp h
  rw [T.th_mul S.z (z_mem_M S) t ht, T.th_z] at h1
  exact qts_line_parts.2.2.2.2 _ (T.th_mem_sl hS.weak ht htz hne) h1

end Chart

end CFSG.LargeExtraspecial.AS35QTS
