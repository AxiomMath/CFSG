module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Th.S.Chars
public import CFSG.Sporadic.Bridge.ThData

set_option maxRecDepth 400000

#th_chars CFSG.KD.ThSj.LI CFSG.Sporadic.Bridge.Th.imgText
#th_chars CFSG.KD.ThSj.LS CFSG.Sporadic.Bridge.Th.stdText

#kc_repo #kc_nat_items_gz CFSG.KD.ThSj "CFSG/Certificates/Kernel/Th/S/Data/data/Surj_const.items.gz"
    127028 14685909547734755133
    (R 0 17)
#kc_repo #kc_json_family_gz CFSG.KD.ThSj "CFSG/Certificates/Kernel/Th/S/Data/data/Surj_lists.json.gz"
    191 16704446367998811902
    (S : List Nat)

#kc_select CFSG.KD.ThSj RB R 17
